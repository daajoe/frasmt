#!/usr/bin/env python
#
# Copyright 2018, 2019, 2020

#
# fhtw.py is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.  fhtw.py is distributed in
# the hope that it will be useful, but WITHOUT ANY WARRANTY; without
# even the implied warranty of MERCHANTABILITY or FITNESS FOR A
# PARTICULAR PURPOSE.  See the GNU General Public License for more
# details.  You should have received a copy of the GNU General Public
# License along with fhtw.py.  If not, see
# <http://www.gnu.org/licenses/>.

from __future__ import absolute_import

import logging
import re
import subprocess
import tempfile
import time
from decimal import Decimal
# import htd_validate
from io import StringIO
from itertools import combinations
import os

# noinspection PyUnresolvedReferences
from htd_validate.decompositions import FractionalHypertreeDecomposition


# TODO: make more general so that we can call multiple solvers
class FractionalHypertreeDecompositionCommandline(object):
    def __init__(self, hypergraph, wprecision=20, timeout=0, stream=StringIO(), checker_epsilon=None, ghtd=False,
                 solver_bin=None):
        if solver_bin is None:
            logging.error("Solver binary not given. Exiting...")
            raise RuntimeError
        else:
            if not os.path.isfile(solver_bin):
                logging.error(f"File {solver_bin} does not exist. Exiting...")
                exit(1)
            if not os.access(solver_bin, os.X_OK):
                logging.error(f"File {solver_bin} is not executable. Exiting...")
                exit(1)
            self.solver_bin = solver_bin

        if not checker_epsilon:
            checker_epsilon = Decimal(0.001)
        self.__checker_epsilon = checker_epsilon
        self.hypergraph = hypergraph
        self.num_vars = 0
        self.num_cls = 0
        self.timeout = timeout
        self.ord = None
        self.arc = None
        self.weight = None

        self.__clauses = []
        self._vartab = {}
        self.stream = stream
        self.cards = []
        self.wprecision = wprecision
        self.stream.write('(set-option :print-success true)\n(set-option :produce-models true)\n')
        self.ghtd = ghtd

    def prepare_vars(self):
        n = self.hypergraph.number_of_nodes()
        m = self.hypergraph.number_of_edges()

        # self.ord = np.zeros((n + 1, n + 1), dtype=int)
        self.ord = [[None for j in range(n + 1)] for i in range(n + 1)]
        # ordering
        for i in range(1, n + 1):
            # TODO: so far more variables
            for j in range(i + 1, n + 1):
                # for j in range(i + 1, n + 1):
                # (declare-const ord_ij Bool)
                self.ord[i][j] = self.add_var(name='ord_%s_%s' % (i, j))
                self.stream.write(f"(declare-const ord_{i}_{j} Bool)\n")

        # print self.hypergraph.nodes()
        # print n
        # print len(self.ord)
        # print self.ord
        # print self.hypergraph.edges()
        # exit(1)

        # arcs
        self.arc = [[None for j in range(n + 1)] for i in range(n + 1)]
        # self.arc = np.zeros((n + 1, n + 1), dtype=int)
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                # declare arc_ij variables
                self.arc[i][j] = self.add_var(name='arc_%s_%s' % (i, j))
                self.stream.write(f"(declare-const arc_{i}_{j} Bool)\n")

        # weights
        self.weight = [[None for ej in range(m + 1)]
                       for j in range(n + 1)]

        for j in range(1, n + 1):
            for ej in range(1, m + 1):
                # (declare-const weight_j_e Real)
                self.weight[j][ej] = self.add_var(name='weight_%s_e%s' % (j, ej))
                if self.ghtd:
                    self.stream.write(f"(declare-const weight_{j}_e{ej} Int)\n")
                else:
                    self.stream.write(f"(declare-const weight_{j}_e{ej} Real)\n")

                self.stream.write(f"(assert (<= weight_{j}_e{ej} 1))\n")
                self.stream.write(f"(assert (>= weight_{j}_e{ej} 0))\n")

    # z3.Real
    def add_var(self, name):
        vid = self.num_vars

        self._vartab[vid] = name
        self.num_vars += 1
        return vid

    def add_cards(self, C):
        self.cards.append(C)

    def literal_str(self, x):
        if x < 0:
            ret = '(not %s)' % self._vartab[abs(x)]
        else:
            ret = '%s' % self._vartab.get(x)
        return ret

    def add_clause(self, C):
        # C = map(neg, C)
        # self.stream.write("%s 0\n" %" ".join(map(str,C)))
        self.stream.write("(assert (or %s))\n" % (' '.join([self.literal_str(x) for x in C])))
        self.num_cls += 1

    # prepare variables
    def fractional_counters(self, m=None):
        n = self.hypergraph.number_of_nodes()

        logging.info("Counter for fractional covers value=%s" % m)
        for j in range(1, n + 1):
            C0 = []
            weights = []
            for e in self.hypergraph.edges():
                assert (e > 0)
                C0.append(self.weight[j][e])
                weights.append("weight_{j}_e{e}".format(j=j, e=e))

            # set optimization variable or value for SAT check
            # C = [self.literal(x) for x in C0]
            # f = (Sum(C) <= m)
            # logging.debug("Assertation %s" % f)
            # self.__solver.add(f)
            # set optimization variable or value for SAT check
            if m is None:
                m = 'm'
                if self.ghtd:
                    self.stream.write("(declare-const m Int)\n")
                else:
                    self.stream.write("(declare-const m Real)\n")
            if len(weights) > 1:
                self.stream.write(
                    "(assert ( <= (+ {weights}) {m}))\n".format(weights=" ".join(weights), m=m))
            elif len(weights) == 1:
                self.stream.write(f"(assert (<= {weights[0]} {m}))\n")

    def elimination_ordering(self, n):
        tord = lambda p, q: f"ord_{p}{q}" if p < q \
            else f"(not ord_{q}{p})"

        logging.info('Ordering')
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue
                for l in range(1, n + 1):
                    if i == l or j == l:
                        continue
                    # OLD VERSION
                    C = []
                    C.append(-self.ord[i][j] if i < j else self.ord[j][i])
                    C.append(-self.ord[j][l] if j < l else self.ord[l][j])
                    C.append(self.ord[i][l] if i < l else -self.ord[l][i])
                    self.add_clause(C)

        logging.info('Edges')
        # OLD VERSION
        # for e in self.hypergraph.edges():
        #     # PRIMAL GRAPH CONSTRUCTION
        #     for i, j in combinations(self.hypergraph.get_edge(e), 2):
        #         if i < j:
        #             self.add_clause([-self.ord[i][j], self.arc[i][j]])
        #             self.add_clause([self.ord[i][j], self.arc[j][i]])
        for e in self.hypergraph.edges():
            # PRIMAL GRAPH CONSTRUCTION
            for i, j in combinations(self.hypergraph.get_edge(e), 2):
                if i > j:
                    i, j = j, i
                if i < j:
                    # AS CLAUSE
                    self.add_clause([self.ord[i][j], self.arc[j][i]])
                    self.add_clause([-self.ord[i][j], self.arc[i][j]])

        logging.info('Edges Elimintation')
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue
                for l in range(j + 1, n + 1):
                    if i == l:
                        continue

                    # AS CLAUSE
                    self.add_clause([-self.arc[i][j], -self.arc[i][l], -self.ord[j][l], self.arc[j][l]])
                    self.add_clause([-self.arc[i][j], -self.arc[i][l], self.ord[j][l], self.arc[l][j]])
                    # redundant
                    self.add_clause([-self.arc[i][j], -self.arc[i][l], self.arc[j][l], self.arc[l][j]])

        logging.info('Forbid Self Loops')
        # forbid self loops
        for i in range(1, n + 1):
            # self.__solver.add_assertion(Not(self.literal(self.arc[i][i])))
            # self.stream.write("(assert (not arc_{i}_{i}))\n".format(i=i))
            self.add_clause([-self.arc[i][i]])

    def cover(self, n):
        # If a vertex j is in the bag, it must be covered:
        # assert (=> arc_ij  (>= (+ weight_j_e2 weight_j_e5 weight_j_e7 ) 1) )
        # TODO: double-check the iterator over i
        logging.info('Vertex in bag -> covered')
        logging.debug("Edges %s" % self.hypergraph.edges())
        for i in range(1, n + 1):
            for j in range(1, n + 1):
                if i == j:
                    continue

                logging.debug(f"i={i}, j={j}")
                logging.debug(f"edges: {self.hypergraph.edges()}")

                # arc_ij then j must be covered by some edge (because j will end up in one bag)
                weights = []
                C = []
                for e in self.hypergraph.incident_edges(j):
                    logging.debug(" i=%s, j=%s, e=%s" % (i, j, e))
                    C.append(self.weight[i][e])
                    weights.append(f"weight_{i}_e{e}")

                if len(weights) > 1:
                    self.stream.write(
                        "(assert (=> arc_{i}_{j} (>= (+ {weights}) 1)))\n".format(i=i, j=j, weights=" ".join(weights)))
                elif len(weights) == 1:
                    self.stream.write(
                        "(assert (=> arc_{i}_{j} (>= {weights} 1)))\n".format(i=i, j=j, weights=weights[0]))

                # arc_ij then i most be covered by some edge (because i will end up in one bag)
                weights = []
                C = []
                for e in self.hypergraph.incident_edges(i):
                    logging.debug(" i=%s, j=%s, e=%s" % (i, j, e))
                    C.append(self.weight[i][e])
                    weights.append(f"weight_{i}_e{e}")

                if len(weights)>1:
                    self.stream.write(
                        "(assert (>= (+ {weights}) 1))\n".format(weights=" ".join(weights)))
                elif len(weights) == 1:
                    self.stream.write("(assert (>= {} 1))\n".format(weights[0]))
        # assert (=> arc_ij  (>= (+ weight_j_e2 weight_j_e5 weight_j_e7 ) 1) )

    def break_clique(self, clique):
        if clique:
            # Vertices not in the clique are ordered before the clique
            for i in self.hypergraph.nodes():
                if i in clique:
                    continue
                for j in clique:
                    if i < j:
                        self.add_clause([self.ord[i][j]])
                    else:
                        self.add_clause([-self.ord[j][i]])

            # Vertices of the clique are ordered lexicographically
            for i in clique:
                for j in clique:
                    if i != j:
                        if i < j:
                            self.add_clause([self.ord[i][j]])
                        # else:
                        #     self.add_clause([-self.ord[j][i]])

    # twins is a list of list of vertices that are twins
    def encode_twins(self, twin_iter, clique):
        logging.info("Hypergraph %s" % self.hypergraph.number_of_nodes())
        if not clique:
            clique = []
        if twin_iter:
            # vertices of a twin class are order lexicographically
            for twins in twin_iter:
                logging.info("Twins are %s" % twins)
                if len(twins) <= 1:
                    continue
                for i in twins:
                    if i in clique:
                        continue
                    for j in twins:
                        if i != j:
                            if j in clique:
                                continue
                            logging.info("i={i}, j={j}".format(i=i, j=j))
                            logging.info("ord=%s,%s" % (len(self.ord), len(self.ord[0])))
                            if i < j:
                                self.add_clause([self.ord[i][j]])
                                # self.stream.write("(assert (ord_{i}_{j}))\n".format(i=i, j=j))
                            # else:
                            #     self.add_clause([-self.ord[j][i]])
                            #     self.stream.write("(assert (-ord_{j}{i}))\n".format(i=i, j=j))

    def encode(self, clique=None, twins=None):
        n = self.hypergraph.number_of_nodes()

        self.elimination_ordering(n)
        self.cover(n)
        self.break_clique(clique=clique)
        self.encode_twins(twin_iter=twins, clique=clique)

    def configration(self):
        # z3.set_option(html_mode=False)
        # z3.set_option(rational_to_decimal=True)
        # z3.set_option(precision=30)
        # z3.set_option(verbose=1)
        pass

    def _get_ordering(self, model):
        def cmp(i, j):
            if i < j:
                return -1 if model[self.literal(self.ord[i][j])] else 1
            else:
                return 1 if model[self.literal(self.ord[j][i])] else -1

        logging.info("Reconstruct Ordering")

        ordering = range(1, self.hypergraph.number_of_nodes() + 1)
        return sorted(ordering, cmp=cmp)

    def solve(self, m=None, lbound=1, ubound=None, clique=None, twins=None):
        opt = False
        if not m:
            opt = True
        if not ubound:
            ubound = len(self.hypergraph.edges())
        logging.info("WE ARE SOLVING FOR fraction = %s" % m)

        self.prepare_vars()
        self.configration()

        enc_wall = time.time()
        self.encode(clique=clique, twins=twins)
        enc_wall = time.time() - enc_wall
        logging.warning("Encoding time %s" % enc_wall)

        logging.info("SMT solving for: %s" % m)
        # assert(False)
        self.fractional_counters(m=m)
        # self.add_all_at_most(m)
        ret = {"objective": "nan", "decomposition": None, 'enc_wall': enc_wall,
               "smt_solver_stats": None, "smt_objective": "nan"}

        if opt:
            self.encode_opt(opt, lbound=lbound, ubound=ubound)
            # self.stream.write("(check-sat)\n(get-value (m))\n(get-objectives)\n")
            self.stream.write("(check-sat)\n(get-model)\n")

            # TODO: delete configurable
            # TODO: prefix='tmp'[, dir=None
            # TODO: move to shm
            with tempfile.SpooledTemporaryFile() as modelf:
                with tempfile.SpooledTemporaryFile() as errorf:
                    self.run_solver(self.stream, modelf, errorf)

            # decode
            raise NotImplementedError
            res = self.__solver.lower(h)
            logging.warning("SMT solver objective: %s" % res)
            logging.warning("SMT solver objective(lower): %s" % res)

            if str(res) == 'epsilon':
                logging.warning("SMT solver returned confusing objective: %s" % res)
                return ret
            elif str(sat) == "unsat":
                logging.warning("SMT solver returned unsat: %s" % res)
                return ret

            model = self.__solver.model()
            logging.info("SMT Solver model=%s" % model)
            ordering = self._get_ordering(model)
            weights = self._get_weights(model, ordering)

            logging.info("Computed ordering: %s" % ordering)

            fhtd = FractionalHypertreeDecomposition.from_ordering(hypergraph=self.hypergraph, ordering=ordering,
                                                                  weights=weights,
                                                                  checker_epsilon=self.__checker_epsilon)
            # print fhtd
            # encoding = str(self.__solver.statistics)

            # TODO(jf): fixme
            if isinstance(res, z3.IntNumRef):
                rsx = Decimal(res.as_long())
            else:
                rsx = Decimal(res.numerator_as_long()) / Decimal(res.denominator_as_long())

            if lbound == 1 and not rsx - self.__checker_epsilon <= fhtd.width() <= rsx + self.__checker_epsilon:
                raise ValueError("fhtw should be {0}, but actually is {1}".format(rsx, fhtd.width()))
            elif lbound > 1 and rsx + self.__checker_epsilon < fhtd.width():
                raise ValueError("fhtw should be at most {0}, but actually is {1}".format(rsx, fhtd.width()))
            stats = str(self.__solver.statistics())
            regex = re.compile(r"\s*:(?P<group>[A-Za-z\-]+)\s+(?P<val>[0-9]+(\.[0-9]+)*)\s*$")
            res_stats = {}
            for line in stats.split("\n"):
                if line[0] == "(":
                    line = line[1:]
                m = regex.match(line)
                if m:
                    res_stats[m.group("group")] = m.group("val")
            ret.update({"objective": fhtd.width(), "decomposition": fhtd,
                        "smt_solver_stats": res_stats, "smt_objective": str(res)})
            return ret

        else:
            res = self.__solver.check()
            logging.warning("SMT Solver result=%s" % res)
            return {'sat': res}

    def encode_opt(self, opt, lbound=None, ubound=None):
        if opt:
            self.stream.write("(assert (>= m 1))\n")
            self.stream.write("(minimize m)\n")
            if ubound:
                self.stream.write(f"(assert (<= m {ubound}))\n")
            if lbound:
                self.stream.write(f"(assert (>= m {lbound}))\n")

    def decode(self, output, is_z3, htd=False, repair=True):
        ret = {"objective": "nan", "decomposition": None, "arcs": None, "ord": None, "weights": None}

        model = {}

        if not is_z3:
            lines = re.findall('\(([^ ]*) ([a-zA-Z0-9]*)\)', output)

            for nm, val in lines:
                if val == "true":
                    model[nm] = True
                elif val == "false":
                    model[nm] = False
                else:
                    model[nm] = int(val)
        else:
            lines = re.findall('\(define\-fun ([^ ]*) \(\) [a-zA-Z]*\s*([a-zA-Z0-9]*)\)', output)

            for nm, val in lines:
                if val == "true":
                    model[nm] = True
                elif val == "false":
                    model[nm] = False
                else:
                    model[nm] = int(val)

        try:
            ordering = self._get_ordering(model)
            weights = self._get_weights(model, ordering)
            arcs = self._get_arcs(model)
            # edges = self._get_edges(model) if htd else None
            edges = None
            bags = self._get_bags(model) if htd else None
            # edges = None
            # arcs = None
            # edges = None

            htdd = HypertreeDecomposition.from_ordering(hypergraph=self.hypergraph, ordering=ordering,
                                                        weights=weights,
                                                        checker_epsilon=self.__checker_epsilon, edges=edges, bags=bags,
                                                        htd=htd, repair=repair)

            # Debug, verify if the descendent relation is correct
            # if htd:
            #     desc = self._get_desc(model)
            #     for n in htdd.tree.nodes:
            #         actual = set(descendants(htdd.tree, n))
            #         if len(desc[n]) != len(actual) or len(desc[n]-actual) > 0:
            #             print("Failed on node {}, mismatch".format(n, desc[n] - actual))
        #
        # if htd:
        #     eql = self._get_eq(model)
        #
        #     for i, j in eql.iteritems():
        #         print "{}: {}".format(i, j)

        # if htd:
        #     ts = self._get_t(model)
        #     for n in list(htdd.tree.nodes):
        #         if not ts[n]:
        #             #print n
        #             htdd.tree.remove_node(n)

        except KeyError:
            raise ValueError("Could not parse output. In case of mode 2 may indicate unsat, otherwise check error log.")

        # if not htd.validate(self.hypergraph):
        #     raise RuntimeError("Found a GHTD that is not a HTD")

        return DecompositionResult(htdd.width(), htdd, arcs, ordering, weights)


    def _get_weights(self, model, ordering):
        logging.info("Reconstruct weights")
        ret = {}
        n = self.hypergraph.number_of_nodes()
        logging.debug(" Model = %s" % model)
        for i in range(1, n + 1):
            # print 'bag %i'
            ret[i] = {}
            for e in self.hypergraph.edges():
                assert (e > 0)
                val = model[self.literal(self.weight[i][e])]
                # print self.literal(self.weight[i][e]), "vs", model[self.literal(self.weight[i][e])]
                logging.debug(" Mod weight_{i}_e{j}={val}".format(i=i, j=e, val=val))
                # print model
                # print "Mod weight_{i}_e{j}={val}".format(i=i, j=e, val=val)
                if self.ghtd:
                    ret[i][e] = val.as_long()
                else:
                    ret[i][e] = float(val.numerator_as_long()) / float(val.denominator_as_long())
                # print dir(model[self._vartab.get(m)])
                # print float(model[self._vartab.get(m)].numerator_as_long()) / float(model[self._vartab.get(m)].denominator_as_long())
                # print "weight_{i}_e{j}={val} ".format(i=i, j=e, val=val),
                # print val, " vs ", ret[i][e], val.numerator_as_long(), val.denominator_as_long()

        last_vertex = ordering[-1]
        incident_edges = self.hypergraph.incident_edges(last_vertex).keys()
        if len(incident_edges) == 0:
            raise TypeError("Fractional Hypertree Decompositions for graphs with isolated vertices.")

        logging.debug("Weights = %s" % ret)
        return ret

    def run_solver(self, inp_stream, modelf, errorf):
        # print(inp_stream.getvalue())
        # exit(1)

        solver_name = subprocess.check_output([self.solver_bin, "-version"]).decode()
        logging.debug(f"Solver Name: {solver_name}")
        solver_name = solver_name.split(' ')[0]
        # p_solver = Popen(run_cmd, stdout=PIPE, stderr=PIPE, shell=True, close_fds=True, cwd=outdir)
        # inpf.seek(0)
        if 'z3' in solver_name:
            p1 = subprocess.Popen([self.solver_bin, '-smt2', '-in'], stdin=subprocess.PIPE, stdout=modelf, stderr=errorf, shell=True)
            is_z3 =True
        elif 'MathSAT5' in solver_name:
            p1 = subprocess.Popen([self.solver_bin], stdin=subprocess.PIPE, stdout=modelf, stderr=errorf, shell=True)
            is_z3 = False
        else:
            logger.error(f"Unknown solver {solver_name}")
            raise RuntimeError

        p1.communicate(input=inp_stream.getvalue().encode())
        errorf.seek(0)
        # if err != b'':
        #     logging.error(err)
        #     exit(1)
        modelf.seek(0)
        output = modelf.readlines()

        stored_file = False
        for line in output:
            line = line.decode().split('\n')[0]
            if line == 'success':
                continue
            if 'error' in line:
                with tempfile.NamedTemporaryFile(delete=False) as inpf:
                    inpf.write(inp_stream.getvalue().encode())
                    logging.error(f"Solver reported an error. Encoding stored in {inpf.name}")

            print(line)



        exit(1)
        self.decode(output.decode(),is_z3=is_z3)
