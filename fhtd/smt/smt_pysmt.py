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
import logging
import sys
import time
from itertools import ifilter, combinations
from operator import neg

import networkx as nx
import numpy as np
from pysmt.shortcuts import Symbol, Solver, Or, Not, Plus, Real, Implies, And, GE, LE, LT, Min
from pysmt.typing import BOOL, REAL


class FractionalHypertreeDecomposition_pysmt(object):
    def __init__(self, hypergraph, timeout=0, stream=sys.stdout):
        self.hypergraph = hypergraph
        self.num_vars = 1
        self.num_cls = 0
        self.timeout = timeout
        self.ord = None
        self.arc = None
        self.weight = None

        self.__solver = Solver(name="z3", logic="QF_LIA")
        self.__clauses = []
        self._vartab = {}
        self.stream = stream
        self.cards = []

    def prepare_vars(self):
        n = self.hypergraph.number_of_nodes()
        m = self.hypergraph.number_of_edges()

        # self.ord = np.zeros((n + 1, n + 1), dtype=int)
        self.ord = [[None for j in range(n + 1)] for i in range(n + 1)]
        # ordering
        for i in xrange(1, n + 1):
            # TODO: so far more variables
            for j in xrange(i + 1, n + 1):
                # for j in xrange(i + 1, n + 1):
                # (declare-const ord_ij Bool)
                self.stream.write("(declare-const ord_{i}{j} Bool)\n".format(i=i, j=j))
                self.ord[i][j] = self.add_var(name='ord[%s][%s]' % (i, j), dtype=BOOL)

        # arcs
        self.arc = [[None for j in range(n + 1)] for i in range(n + 1)]
        # self.arc = np.zeros((n + 1, n + 1), dtype=int)
        for i in xrange(1, n + 1):
            for j in xrange(1, n + 1):
                # declare arc_ij variables
                self.stream.write("(declare-const arc_{i}{j} Bool)\n".format(i=i, j=j))
                self.arc[i][j] = self.add_var(name='arc[%s][%s]' % (i, j), dtype=BOOL)

        # weights
        self.weight = [[None for e in xrange(m + 1)]
                       for j in xrange(n + 1)]

        for j in xrange(1, n + 1):
            for e in xrange(1, m + 1):
                # (declare-const weight_j_e Real)
                self.stream.write("(declare-const weight_{i}_e{j} Real)\n".format(i=j, j=e))
                self.weight[j][e] = self.add_var(name='weight[%s][e%s]' % (j, e), dtype=REAL)
                self.stream.write("(assert (<= weight_{i}_e{j} 1))\n".format(i=j, j=e))
                self.stream.write("(assert (>= weight_{i}_e{j} 0))\n".format(i=j, j=e))

                self.__solver.add_assertion(LE(self.literal(self.weight[j][e]), Real(1)))
                self.__solver.add_assertion(GE(self.literal(self.weight[j][e]), Real(0)))

        # # cards
        # for i in self.hypergraph.nodes_iter():
        #     C = set()
        #     for j in xrange(1, n + 1):
        #         C.add(self.arc[i][j])
        #     self.add_cards(list(C))


    def add_cards(self, C):
        self.cards.append(C)

    # z3.Real
    def add_var(self, name, dtype=BOOL):
        vid = self.num_vars
        symb = Symbol(name=name, typename=dtype)
        logging.debug("Add Variable %s=(%s)" % (vid, symb))
        self._vartab[vid] = symb
        self.num_vars += 1
        return vid

    def literal(self, x):
        logging.debug("Literal %s (var: %s)" % (x, self._vartab[abs(x)]))
        return Not(self._vartab[abs(x)]) if x < 0 else self._vartab.get(x)

    def add_clause(self, C):
        # C = map(neg, C)
        # self.stream.write("%s 0\n" %" ".join(map(str,C)))
        f = Or([self.literal(x) for x in C])
        self.__solver.add_assertion(f)
        self.num_cls += 1

    # prepare variables
    def fractional_counters(self, m=None):
        n = self.hypergraph.number_of_nodes()
        # TODO: fixme
        # JF: CONTINUE HERE TOMORROW
        # And, of course, we limit the total weight of the fractional cover, say to 5.
        # (assert (<= (+ weight_j_e1 weight_j_e2 weight_j_e3 weight_j_e4  ) 5))
        opt = False
        if not m:
            # m = Real()
            var = self.add_var("m", REAL)
            m = self._vartab[var]
            opt = True
            logging.critical("THE pysmt API seemingly does not support optimization. "
                             "Use the Z3 API!")
            raise NotImplementedError
        else:
            m = Real(m)

        logging.info("Counter for fractional covers value=%s" % m)
        for j in xrange(1, n + 1):
            C = []
            weights = []
            for e in self.hypergraph.edges():
                C.append(self.weight[j][e])
                weights.append("weight_{j}_e{e}".format(j=j, e=e))

            C = [self.literal(x) for x in C]
            f = LE(Plus(C), m)
            logging.info("Assertation %s" % f)
            self.__solver.add_assertion(f)

            self.stream.write(
                "(assert ( <= (+ {weights}) {m}))\n"
                    .format(weights=" ".join(weights), m=m))
        if opt:
            self.__solver.solve(Min(m))
            # self.__solver.add_assertion()

    def add_at_most(self, C, m):
        self.backend.add_weight_rule(head=[], lower=m + 1, body=[(x, 1) for x in C], choice=False)
        # self.stream.write("%s <= %i0\n" % (" ".join(map(lambda x: str(int(x)),C)),m))

    def add_seq_at_most(self, C, k):
        logging.info("  Sinz Cardinality Encoding %s" %k)
        logging.info("cards %s" %C)

        n = len(C)
        # TODO: crappy fix due to index error
        C.insert(0, 0)
        R = np.zeros((n + 1, k + 1), dtype=int)
        for i in xrange(1, n + 1):
            for j in xrange(1, k + 1):
                R[i][j] = self.add_var(name='R[%s][%s]' % (i, j), dtype=BOOL)

        for i in xrange(1, n):
            self.add_clause([-C[i], R[i][1]])

        # eqn 2
        for j in xrange(2, k + 1):
            self.add_clause([-R[1][j]])

        # eqn 3
        for i in xrange(2, n):
            for j in xrange(1, k + 1):
                self.add_clause([-R[i - 1][j], R[i][j]])

        # eqn 4
        for i in xrange(2, n):
            for j in xrange(2, k + 1):
                self.add_clause([-C[i], -R[i - 1][j - 1], R[i][j]])

        # eqn 5
        for i in xrange(2, n + 1):
            self.add_clause([-C[i], -R[i - 1][k]])

        # TODO: see above index error
        C.pop(0)

        ##mark aux vars
        ##for i in xrange(1, len(C)+1):
        ##   for j in xrange(1, k+1):
        ##       mark_aux(R[i][j])

    def add_all_at_most(self, m):
        logging.info("Adding cardinality constraints")
        for C in self.cards:
            # self.add_at_most(C, m)
            self.add_seq_at_most(C,m)
            # add_bin_at_most(C,m)

    def elimination_ordering(self, n):
        ord = lambda p, q: self.literal(self.ord[p][q]) if p < q else Not(self.literal(self.ord[q][p]))
        tord = lambda p, q: 'ord_{p}{q}'.format(p=p, q=q) if p < q \
            else '(not ord_{q}{p})'.format(p=p, q=q)

        logging.info('Ordering')
        for i in xrange(1, n + 1):
            for j in xrange(1, n + 1):
                if i == j:
                    continue
                for l in xrange(1, n + 1):
                    if i == l or j == l:
                        continue
                    # OLD VERSION
                    C = []
                    C.append(-self.ord[i][j] if i < j else self.ord[j][i])
                    C.append(-self.ord[j][l] if j < l else self.ord[l][j])
                    C.append(self.ord[i][l] if i < l else -self.ord[l][i])
                    self.add_clause(C)
                    # IMPLIES VERSION
                    # (assert (=> (and ord_ij ord_jl) ord_il)

                    # logging.debug(
                    #     "i=%s j=%s l=%s ord[i][j]=%s, ord[j][l]=%s" % (i, j, l, self.ord[i][j], self.ord[j][l]))
                    # f = Implies(And(ord(i, j), ord(j, l)), ord(i, l))
                    # Or([self.literal(x) for x in C])
                    # self.__solver.add_assertion(f)
                    # (assert (=> (and ord_ij ord_jl) ord_il)
                    self.stream.write(
                        "(assert (=> (and ord_{i}{j} ord_{j}{l}) ord_{i}{l}))\n".format(i=i, j=j, l=l))
                    self.stream.write(
                        "(assert (=> (and %s %s) %s))\n" % (tord(i, j), tord(j, l), tord(i, l)))

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
                if i>j:
                    i, j = j, i
                if i < j:
                    # AS IMPLICATION
                    # f = Implies(self.literal(self.ord[i][j]), self.literal(self.arc[i][j]))
                    # self.__solver.add_assertion(f)
                    # f = Implies(Not(self.literal(self.ord[i][j])), self.literal(self.arc[j][i]))
                    # self.__solver.add_assertion(f)

                    self.stream.write("(assert (=> ord_{i}{j} arc_{i}{j}))\n".format(i=i, j=j))
                    self.stream.write("(assert (=> (not ord_{i}{j}) arc_{j}{i}))\n".format(i=i, j=j))

                    # AS CLAUSE
                    self.add_clause([-self.ord[i][j], self.arc[i][j]])
                    self.add_clause([self.ord[i][j], self.arc[j][i]])

        logging.info('Edges Elimintation')
        for i in xrange(1, n + 1):
            for j in xrange(1, n + 1):
                if i == j:
                    continue
                for l in xrange(j + 1, n + 1):
                    if i == l:
                        continue
                    # # AS IMPLICATION
                    # f = Implies(And(self.literal(self.arc[i][j]),
                    #                 And(self.literal(self.arc[i][l]), self.literal(self.ord[j][l]))),
                    #             self.literal(self.arc[j][l]))
                    # self.__solver.add_assertion(f)
                    # self.stream.write(
                    #     "(assert (=> (and arc_{i}{j} arc_{i}{l} ord_{j}{l}) arc_{j}{l}))\n".format(i=i, j=j, l=l))
                    #
                    # f = Implies(And(self.literal(self.arc[i][j]),
                    #                 And(self.literal(self.arc[i][l]), Not(self.literal(self.ord[j][l])))),
                    #             self.literal(self.arc[l][j]))
                    # self.__solver.add_assertion(f)
                    self.stream.write(
                        "(assert (=> (and arc_{i}{j} arc_{i}{l} (not ord_{j}{l})) arc_{l}{j}))\n".format(i=i, j=j, l=l))
                    #
                    # # redundant
                    # f = Or(Not(self.literal(self.arc[i][j])), Or(Not(self.literal(self.arc[i][l])),
                    #                                              Or(self.literal(self.arc[j][l]),
                    #                                                 self.literal(self.arc[l][j]))))
                    # self.__solver.add_assertion(f)
                    self.stream.write(
                        "(assert (or (not arc_{i}{j}) (not arc_{i}{l}) arc_{j}{l} arc_{l}{j}))\n".format(i=i, j=j, l=l))

                    # AS CLAUSE
                    self.add_clause([-self.arc[i][j], -self.arc[i][l], -self.ord[j][l], self.arc[j][l]])
                    self.add_clause([-self.arc[i][j], -self.arc[i][l], self.ord[j][l], self.arc[l][j]])
                    # redunant
                    self.add_clause([-self.arc[i][j], -self.arc[i][l], self.arc[j][l], self.arc[l][j]])

        logging.info('Forbid Self Loops')
        # forbid self loops
        for i in xrange(1, n + 1):
            # self.__solver.add_assertion(Not(self.literal(self.arc[i][i])))
            self.stream.write("(assert (not arc_{i}{i}))\n".format(i=i))
            self.add_clause([-self.arc[i][i]])

    def cover(self, n):
        # If a vertex j is in the bag, it must be covered:
        # assert (=> arc_ij  (>= (+ weight_j_e2 weight_j_e5 weight_j_e7 ) 1) )
        # TODO: double-check the iterator over i
        logging.info('Vertex in bag -> covered')
        for i in xrange(1, n + 1):
            for j in xrange(1, n + 1):
                logging.debug("i=%s, j=%s" % (i, j))
                if i == j:
                    continue

                logging.debug("" % self.hypergraph.edges())

                #i part
                weights = []
                C = []
                for e in self.hypergraph.incidence_edges(j):
                    logging.debug("j=%s, e=%s" % (j, e))
                    C.append(self.weight[j][e])
                    weights.append("weight_{j}_e{e}".format(j=j, e=e))

                C = [self.literal(x) for x in C]
                f = Implies(self.literal(self.arc[i][j]), GE(Plus(C), Real(1.0)))
                self.__solver.add_assertion(f)
                self.stream.write(
                    "(assert (=> arc_{i}{j} (>= (+ {weights}) 1)))\n".format(i=i, j=j, weights=" ".join(weights)))

                #j part
                weights = []
                C = []
                for e in self.hypergraph.incidence_edges(i):
                    logging.debug("j=%s, e=%s" % (i, e))
                    C.append(self.weight[j][e])
                    weights.append("weight_{j}_e{e}".format(j=j, e=e))

                C = [self.literal(x) for x in C]
                f = Implies(self.literal(self.arc[i][j]), GE(Plus(C), Real(1.0)))
                self.__solver.add_assertion(f)
                self.stream.write(
                    "(assert (=> arc_{i}{j} (>= (+ {weights}) 1)))\n".format(i=i, j=j, weights=" ".join(weights)))


                # assert (=> arc_ij  (>= (+ weight_j_e2 weight_j_e5 weight_j_e7 ) 1) )

    def break_clique(self, clique):
        raise NotImplementedError
        if clique:
            for i in self.hypergraph.nodes_iter():
                if i in clique:
                    continue
                for j in clique:
                    if (i < j):
                        self.add_clause([self.ord[i][j]])
                    else:
                        self.add_clause([-self.ord[j][i]])

        # vertices of the clique are order lexicographically
        for i in clique:
            for j in clique:
                if i < j:
                    if i < j:
                        self.add_clause([self.ord[i][j]])
                    else:
                        self.add_clause(-self.ord[j][i])

    def encode(self):
        n = self.hypergraph.number_of_nodes()
        self.elimination_ordering(n)
        self.cover(n)

        # encode clique
        # TODO: set timeout
        # from networkx.algorithms import approximation
        # clique = approximation.max_clique(hypergraph)

        # TODO: handling of cliques
        # try:
        #     clique = next(nx.find_cliques(self.hypergraph))
        #     print 'clique', clique
        #     self.break_clique(clique)
        # except StopIteration:
        #     print 'no clique'
        #     pass

        # for clique in nx.find_cliques(hypergraph):
        # TODO: twin decomposition

    def configration(self):
        # z3.set_option(verbose=1)
        pass

    def solve(self, m=None):
        logging.info("WE ARE SOLVING FOR fraction = %s" % m)
        self.prepare_vars()
        self.configration()

        self.encode()
        print self.__solver.check()
        print self.__solver.model()

        self.fractional_counters(m)
        # self.add_all_at_most(m)

        print "*" * 80

        ret = self.__solver.solve()
        logging.warning("SMT Solver result=%s" %ret)
        if ret:
            print()
            print "*" * 80
            print(self.__solver.get_model())
        # print(self.__solver.statistics())

    @property
    def treewidth(self):
        start = time.time()
        print 'encode'
        self.encode()
        elapsed = time.time() - start
        print 'encode finished'
        print 'encoding time = %s' % elapsed
        # timeout = self.timeout
        timeout = 0

        for m in xrange(self.ubound, 0, -1):
            timeout = np.ceil(timeout)
            start = time.time()
            print '=' * 80
            print 'm=%s, timeout=%s' % (m, timeout)
            self.fractional_counters(m)
            f = self.ctl.solve_async()  # on_model, on_finish)
            done = f.wait(timeout)
            diff = time.time() - start
            if timeout != 0 and not done:
                f.cancel()
                if timeout < diff:
                    timeout = timeout / 0.97

                print '-' * 20, 'minor', '-' * 20
                # TODO:
                # self.minor_lbound(6, m)
                res = self.minor_lbound_num(m, timeout)
                if not res is None and res == False:
                    print 'solution found=%i' % (m + 1)
                    return m + 1

                    # self.subgraph_lbound(m)
                    # print 'solve=', self.solve(5)
            if timeout == 0:
                timeout = diff
            if timeout < diff:
                timeout = timeout / 0.97

            print f.get().satisfiable
            if not f.get().satisfiable:
                print 'solution found=',
                print m + 1
                return m + 1
