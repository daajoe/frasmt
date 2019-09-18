#!/usr/bin/env python
#
# Copyright 2017

#
# vc_clasp.py is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.  vc_clasp.py is distributed in
# the hope that it will be useful, but WITHOUT ANY WARRANTY; without
# even the implied warranty of MERCHANTABILITY or FITNESS FOR A
# PARTICULAR PURPOSE.  See the GNU General Public License for more
# details.  You should have received a copy of the GNU General Public
# License along with vc_clasp.py.  If not, see
# <http://www.gnu.org/licenses/>.
import argparse
import clingo
import fileinput
import logging
from copy import deepcopy
from itertools import izip, ifilter
from operator import neg

import networkx as nx
import numpy as np
import os
import sys
import time

from os.path import dirname

# from preprocessing import simplify



class GraphSatTw(object):
    def __init__(self, G, ubound = -1, timeout=0, stream=sys.stdout):
        self.G = G
        # self.ctl = clingo.Control()
        # self.backend = self.ctl.backend
        self.num_vars = 1
        self.num_cls = 0
        self.timeout = timeout
        self.ord = None
        self.arc = None
        self.cards = []
        self.ubound = ubound
        self.stream = stream

        self.prepare_vars()
        # self.configration()

    # store and access is slightly faster
    # def my_ord(i,j,offset=0):
    #    return (n*(n-1)/2) - ((n-i)*((n-i)+1)/2) + (j-i)

    def prepare_vars(self):
        n = self.G.number_of_nodes()

        self.ord = np.zeros((n + 1, n + 1), dtype=int)
        # ordering
        for i in xrange(1, n + 1):
            for j in xrange(i + 1, n + 1):
                self.ord[i][j] = self.add_var()

        # arcs
        self.arc = np.zeros((n + 1, n + 1), dtype=int)
        for i in xrange(1, n + 1):
            for j in xrange(1, n + 1):
                self.arc[i][j] = self.add_var()

        # cards
        for i in self.G.nodes_iter():
            C = set()
            for j in xrange(1, n + 1):
                C.add(self.arc[i][j])
            self.add_cards(list(C))

    def add_var(self):
        # self.num_vars = self.backend.add_atom()
        self.num_vars+=1
        return self.num_vars-1

    def add_clause(self, C):
        # C = map(neg, C)
        # self.backend.add_rule(head=[], body=C, choice=False)
        self.stream.write("%s 0\n" %" ".join(map(str,C)))
        self.num_cls += 1

    def add_cards(self, C):
        self.cards.append(C)

    def add_at_most(self, C, m):
        # self.backend.add_weight_rule(head=[], lower=m + 1, body=[(x, 1) for x in C], choice=False)
        self.stream.write("%s <= %i 0\n" % (" ".join(map(lambda x: str(int(x)),C)),m))

    def add_bin_at_most_(self, C, curr, k, pos):
        # subset complete cls
        if k == 0:
            self.add_clause(curr)
        # end
        if pos == len(C):
            return
        # add vars
        for i in xrange(pos, len(C)):
            curr.append(-C[i])
            self.add_bin_at_most_(C, curr, k - 1, i + 1)
            curr.pop()  # len(curr)-1)

    def add_bin_at_most(self, C, k):
        self.add_bin_at_most_(C, [], k + 1, 0)

    # Sinz encoding
    def add_seq_at_most(self, C, k):
        old_num_vars = self.num_vars
        n = len(C)
        # TODO: crappy fix due to index error
        C.insert(0, 0)
        R = np.zeros((n + 1, k + 1), dtype=int)
        for i in xrange(1, n + 1):
            for j in xrange(1, k + 1):
                R[i][j] = self.add_var()

        self.add_choice(range(old_num_vars + 1, self.num_vars + 1))

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

    # prepare variables
    def add_all_at_most(self, m):
        for C in self.cards:
            # self.add_at_most(C, m)
            self.add_seq_at_most(C,m)
            # add_bin_at_most(C,m)

    def add_at_least(self, m):
        for card in izip(self.cards, xrange(len(self.cards))):
            at = self.backend.add_atom()
            # print card, m
            self.backend.add_weight_rule(head=[at], lower=m, body=[(x, 1) for x in card[0]], choice=False)
            # backend.add_rule(head=[], body=[-at],choice=False)

    def add_choice(self, ats):
        return
        for a in ats:
            self.backend.add_rule(head=[a], body=[], choice=True)

    def improved(self, n):
        # the order has to be transitive (3)
        # ADD CLAUSES
        # transitive
        for i in xrange(1, n + 1):
            for j in xrange(1, n + 1):
                if i == j:
                    continue
                for l in xrange(1, n + 1):
                    if i == l or j == l:
                        continue
                    C = []
                    C.append(-self.ord[i][j] if i < j else self.ord[j][i])
                    C.append(-self.ord[j][l] if j < l else self.ord[l][j])
                    C.append(self.ord[i][l] if i < l else -self.ord[l][i])
                    self.add_clause(C)

        # edges
        # edges uv in E have to be in the triangluation (4)
        for i, j in self.G.edges():
            if i < j:
                # improved version
                # add_clause([-self.ord[i][j], self.arc[i][j]])
                self.add_clause([self.ord[i][j], self.arc[j][i]])

        # if u and v have a common predecessor then the graph contains the edge {u,v} (5)
        for i in xrange(1, n + 1):
            for j in xrange(1, n + 1):
                if i == j:
                    continue
                for k in xrange(1, n + 1):
                    if i == k or j == k:
                        continue
                    self.add_clause([-self.arc[k][i], -self.arc[k][j], self.arc[i][j], self.arc[j][i]])

        # uv \in E_T, choice of (u,v) or (v,u) depends on ord (6)
        for i in xrange(1, n + 1):
            for j in xrange(1, n + 1):
                if i == j:
                    continue
                if i < j:
                    self.add_clause([-self.ord[i][j], -self.arc[j][i]])
                else:
                    self.add_clause([self.ord[j][i], -self.arc[j][i]])

        # domain specific redundant clauses (7)
        for i in xrange(1, n + 1):
            for j in xrange(1, n + 1):
                if i == j:
                    continue
                self.add_clause([-self.arc[j][i], -self.arc[i][j]])

    def sv(self, n):
        logging.info('Ordering')
        for i in xrange(1, n + 1):
            for j in xrange(1, n + 1):
                if i == j:
                    continue
                for l in xrange(1, n + 1):
                    if i == l or j == l:
                        continue
                    C = []
                    C.append(-self.ord[i][j] if i < j else self.ord[j][i])
                    C.append(-self.ord[j][l] if j < l else self.ord[l][j])
                    C.append(self.ord[i][l] if i < l else -self.ord[l][i])
                    self.add_clause(C)

        logging.info('Edges')
        for i, j in self.G.edges():
            print(i,j)
            if i < j:
                print("i=", i, "j=", j)
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
                    self.add_clause([-self.arc[i][j], -self.arc[i][l], -self.ord[j][l], self.arc[j][l]])
                    self.add_clause([-self.arc[i][j], -self.arc[i][l], self.ord[j][l], self.arc[l][j]])
                    # redunant
                    self.add_clause([-self.arc[i][j], -self.arc[i][l], self.arc[j][l], self.arc[l][j]])

        logging.info('Forbid Self Loops')
        # forbid self loops
        for i in xrange(1, n + 1):
            self.add_clause([-self.arc[i][i]])

    def break_clique(self, clique):
        if clique:
            for i in self.G.nodes_iter():
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
        n = self.G.number_of_nodes()
        self.sv(n)

        # encode clique
        # TODO: set timeout
        # from networkx.algorithms import approximation
        # clique = approximation.max_clique(G)

        try:
            clique = next(nx.find_cliques(self.G))
            print('clique', clique)
            self.break_clique(clique)
        except StopIteration:
            print('no clique')
            pass

        # for clique in nx.find_cliques(G):
        # TODO: twin decomposition
        self.add_choice(range(1, self.num_vars + 1))

    def configration(self):
        # print ctl.configuration.solver.keys, ctl.configuration.keys, ctl.configuration.solve.keys, ctl.configuration.asp.trans_ext
        # self.ctl.configuration.asp.trans_ext = 'weight'
        # self.ctl.configuration.solver.acyc_prop
        self.ctl.configuration.asp.trans_ext = 'all'

        self.ctl.configuration.configuration = 'trendy'  # 23
        # self.ctl.configuration.configuration='handy' #48
        # self.ctl.configuration.configuration='crafty' #39
        # self.ctl.configuration.configuration='jumpy' #26
        # self.ctl.configuration.configuration='frumpy' #39
        # self.ctl.configuration.configuration='tweety' #38

    def solve(self, m):
        self.encode()
        self.add_all_at_most(m)
        print('m=%s, timeout=%s' % (m, self.timeout))
        # f = self.ctl.solve_async()  # on_model, on_finish)
        # done = f.wait(self.timeout)
        # if not done:
        #     return None
        # return f.get().satisfiable

    # print G.number_of_nodes(), G.number_of_edges()
    # G=contract(G,5)
    # print G.number_of_nodes(), G.number_of_edges()


    def contract(self, G, c):
        # Contract edges uv as long as d(u)+d(v)\leq c.
        while True:
            try:
                u, v = next(ifilter(lambda x: x[0] != x[1] and G.degree(x[0]) + G.degree(x[1]) <= c, G.edges_iter()))
                G = nx.contracted_edge(G, (u, v), self_loops=False)
            except StopIteration:
                break
        return G

    def minor_lbound(self, c, k):
        # Assume we believe that tw(G)> k since we hit a timeout for k.
        G = nx.convert_node_labels_to_integers(self.contract(self.G.copy(), c), first_label=1)

        # Then check for unsatisfiability; if it is unsatisfiable,
        lbound_solver = GraphSatTw(G)
        return lbound_solver.solve(k)
        # solve()

        # then we have confirmed tw(G)> k as by contraction of edges we obtained a minor of G.

        # For c=4 this is just the preprocessing rule for degree 1 and degree 2 vertices.
        # It would be interesting to check the behaviour for, say, c=5 and c=6.

    def minor_lbound_num(self, k, timeout, l=1):
        for u, v in self.G.edges_iter():
            G1 = nx.convert_node_labels_to_integers(nx.contracted_edge(self.G, (u, v), self_loops=False))
            # sanity check
            # G1 = self.G.copy()
            lbound_solver = GraphSatTw(G1, timeout=timeout)

            print('u = %s, v = %s' % (u, v))
            ret = lbound_solver.solve(k)
            print('ret = %s' % ret)
            if not ret:
                return False

        return True

    def subgraph_lbound(self, k):
        for n in self.G.nodes_iter():
            G1 = self.G.copy()
            G1.remove_node(n)
            G1 = nx.convert_node_labels_to_integers(G1, first_label=1)
            # print G1.edges()
            lbound_solver = GraphSatTw(G1)
            res = lbound_solver.solve(k)
            print('node=%s, bound=%s, res=%s' % (n, k, res))

    def extract_assignment(self,assignment):
        pass

    #TODO: static?
    def set_assignment(self,assignment):
        def on_model(model):
            # print model.contains(clingo.Function("volatile", [9])).lower()

            for x in model.symbols(atoms=True):
                print('yyy')
            print('model000=', str(model))
            print('model=', dir(model))
            print('cost=', model.cost)
            assignment[0] = True
            # assignment[0] = deepcopy(model)
            #TODO: does not show any results here
            print('symbols=', model.symbols(atoms=True,terms=True,shown=True,csp=True,extra=True))
        return on_model


    @property
    def treewidth(self):
        start = time.time()
        print('encode')
        self.encode()
        elapsed = time.time() - start
        print('encode finished')
        print('encoding time = %s' % elapsed)
        # timeout = self.timeout
        timeout = 0

        assignment = [None]
        for m in xrange(self.ubound, 0, -1):
            timeout = np.ceil(timeout)
            start = time.time()
            print('=' * 80)
            print('m=%s, timeout=%s' % (m, timeout))
            self.add_all_at_most(m)
            # print 'signatures', self.ctl.symbolic_atoms.signatures

            future = self.ctl.solve_async(on_model=self.set_assignment(assignment))  # on_model, on_finish)
            print('assignment=', assignment)
            done = future.wait(timeout)
            diff = time.time() - start
            if timeout != 0 and not done:
                future.cancel()
                if timeout < diff:
                    timeout = timeout / 0.97

                #print '-' * 20, 'minor', '-' * 20
                # TODO:
                # self.minor_lbound(6, m)
                res = self.minor_lbound_num(m, timeout)
                if not res is None and res == False:
                    print('solution found=%i' % (m + 1))
                    return m + 1

                    # self.subgraph_lbound(m)
                    # print 'solve=', self.solve(5)
            if timeout == 0:
                timeout = diff
            if timeout < diff:
                timeout = timeout / 0.97

            print(future.get().satisfiable)
            if not future.get().satisfiable:
                print('solution found=',)
                print(m + 1)
                return m + 1
            else:
                print('assignment=', assignment)
                pass
                # assignment = self.extract_assignment()


