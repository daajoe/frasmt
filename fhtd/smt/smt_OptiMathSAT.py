#!/usr/bin/env python
#
# Copyright 2018

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
# import htd_validate
from io import StringIO
from decimal import Decimal
from itertools import combinations

import z3
# noinspection PyUnresolvedReferences
from htd_validate.decompositions import FractionalHypertreeDecomposition


# import hypergraph_preprocessing.util as util
# util.import_libs()


class FractionalHypertreeDecomposition_OptiMathSAT(object):
    def __init__(self, hypergraph, wprecision=20, timeout=0, stream=StringIO(), checker_epsilon=None, ghtd=False):
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
                self.stream.write("(declare-const ord_{i}_{j} Bool)\n".format(i=i, j=j))

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
                self.stream.write("(declare-const arc_{i}_{j} Bool)\n".format(i=i, j=j))

        # weights
        self.weight = [[None for ej in range(m + 1)]
                       for j in range(n + 1)]

        for j in range(1, n + 1):
            for ej in range(1, m + 1):
                # (declare-const weight_j_e Real)
                self.weight[j][ej] = self.add_var(name='weight_%s_e%s' % (j, ej))
                if self.ghtd:
                    self.stream.write("(declare-const weight_{i}_e{ej} Int)\n".format(i=j, ej=ej))
                else:
                    self.stream.write("(declare-const weight_{i}_e{ej} Real)\n".format(i=j, ej=ej))

                self.stream.write("(assert (<= weight_{i}_e{ej} 1))\n".format(i=j, ej=ej))
                self.stream.write("(assert (>= weight_{i}_e{ej} 0))\n".format(i=j, ej=ej))

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
            if len(weights) > 1:
                self.stream.write(
                    "(assert ( <= (+ {weights}) {m}))\n".format(weights=" ".join(weights), m=m))
            elif len(weights) == 1:
                self.stream.write("(assert (<= {} {}))\n".format(weights[0], m))

    def elimination_ordering(self, n):
        tord = lambda p, q: 'ord_{p}{q}'.format(p=p, q=q) if p < q \
            else '(not ord_{q}{p})'.format(p=p, q=q)

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

                # TODO: add i>j
                logging.debug("i=%s, j=%s" % (i, j))
                logging.debug("edges: %s" % self.hypergraph.edges())

                # arc_ij then j must be covered by some edge (because j will end up in one bag)
                weights = []
                C = []
                for e in self.hypergraph.incident_edges(j):
                    logging.debug(" i=%s, j=%s, e=%s" % (i, j, e))
                    C.append(self.weight[i][e])
                    weights.append("weight_{i}_e{e}".format(i=i, e=e))

                # TODO: continue HERE

                # C = [self.literal(x) for x in C]
                # f = Implies(self.literal(self.arc[i][j]), (Sum(C) >= 1.0))
                # logging.debug(" Assertation %s" % f)
                # self.__solver.add(f)
                self.stream.write(
                    "(assert (=> arc_{i}_{j} (>= (+ {weights}) 1)))\n".format(i=i, j=j, weights=" ".join(weights)))

                # arc_ij then i most be covered by some edge (because i will end up in one bag)
                weights = []
                C = []
                for e in self.hypergraph.incident_edges(i):
                    logging.debug(" i=%s, j=%s, e=%s" % (i, j, e))
                    C.append(self.weight[i][e])
                    weights.append("weight_{i}_e{e}".format(i=i, e=e))

                # C = [self.literal(x) for x in C]
                # f = (Sum(C) >= 1.0)
                # logging.debug(" Assertation %s" % f)

                # self.__solver.add(f)
                self.stream.write(
                    "(assert (>= (+ {weights}) 1))\n".format(weights=" ".join(weights)))
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
            self.encode_opt(opt, lbound=lbound,ubound=ubound)
            self.stream.write("(check-sat)\n(get-value (m))\n(get-objectives)\n")

            #TODO: delete configurable
            #TODO: prefix='tmp'[, dir=None
            with tempfile.SpooledTemporaryFile() as inpf:
                with tempfile.SpooledTemporaryFile() as modelf:
                    with tempfile.SpooledTemporaryFile() as errorf:
                        #TODO: is_z3
                        is_z3 = False
                        slv = "/home/vagrant/bin/optimathsat"
                        self.run_solver(slv, inpf, modelf, errorf, is_z3)

            #decode
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
            if self.ghtd:
                self.stream.write("(declare-const m Int)\n")
            else:
                self.stream.write("(declare-const m Real)\n")
            self.stream.write("(assert (>= m 1))\n")
            self.stream.write("(minimize m)\n")
            if ubound:
                self.stream.write("(assert (<= m {ub}))\n".format(ub=ubound))
            if lbound:
                self.stream.write("(assert (>= m {lb}))\n".format(lb=lbound))

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

    def run_solver(self, slv, inpf, modelf, errorf, is_z3):
        inpf.seek(0)
        if is_z3:
            p1 = subprocess.Popen([slv, '-smt2', '-in'], stdin=inpf, stdout=modelf, stderr=errorf)
        else:
            p1 = subprocess.Popen(slv, stdin=inpf, stdout=modelf, stderr=errorf, shell=True)

        p1.wait()
        # Retrieve the result
        modelf.seek(0)
        errorf.seek(0)
        outp = modelf.read()
        errp = errorf.read()

        if len(errp) > 0:
            raise RuntimeError(errp)

        print(outp)
        print(errp)

        raise NotImplementedError
