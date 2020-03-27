#!/usr/bin/env python
#
# Copyright 2018



#
# fhtd is free software: you can redistribute it
# and/or modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation, either version 3 of
# the License, or (at your option) any later version.
# fhtd is distributed in the hope that it will be
# useful, but WITHOUT ANY WARRANTY; without even the implied warranty
# of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.  You should have received a
# copy of the GNU General Public License along with
# fhtd.  If not, see <http://www.gnu.org/licenses/>.
#
from __future__ import absolute_import

import logging


class FractionalHyperTreeDecomposition_Preprocessor:
    # suggested order [1], ..., [k]
    def __init__(self, hgprimview, replay=True, lb=1):
        self.__lb = lb  # initial lower bound 1
        self.init(hgprimview, replay)

    def init(self, hgprimview, replay=True):
        self.__hgp = hgprimview
        self.__replay = [] if replay else None
        self.__cliques_finished = [] if replay else None

    @property
    def lb(self):
        return self.__lb

    @property
    def replay(self):
        return self.__replay

    # todo: only for internal purposes
    # @lb.setter
    def slb(self, value):
        self.__lb = value

    @property
    def hgp(self):
        return self.__hgp

    def __debug_step(self, state):
        logging.info("{0} {1},{2},{3}".format(state, self.__replay, self.__hgp.nodes(), self.__hgp.hg.edges()))
        # print("{0}\n{1}\n{2}\n{3}".format(state, self.__replay, self.__hgp.nodes(), self.__hgp.hg.edges()))

    def preprocess(self):
        #return (self.__replay, self.__lb)  # , self.__hgp.hg.get_nsymtab().id2name)
        run = True
        while run:
            run = False
            while self.remove_hyper_degree_vertex():
                run = True
            self.__debug_step("post-degree")
            while self.almost_simplicial_hypergraph():
                run = True
            self.__debug_step("post-almost-simplicial")
            while self.simplicial_primalgraph(clique_prevent_he_up_to=10):
                run = True
            self.__debug_step("post-simplicial-primal")
            while self.almost_simplicial_primalgraph(clique_prevent_he_up_to=10):
                run = True
            self.__debug_step("post-almost-simplicial-primal")
        return (self.__replay, self.__lb)  # , self.__hgp.hg.get_nsymtab().id2name)

    def update_finished_cliques(self, contr, erepr):
        for x in self.__cliques_finished:
            if x[1] in contr:
                x[1] = erepr
            x[0] = {xi if xi not in contr else erepr for xi in x[0]}

    def clique_finished(self, clnew, vnew, autoAdd=True):
        # return False
        clnew = {ei for ei in clnew if ei != vnew}
        # print "REQUEST ", self.__cliques_finished, clnew, vnew
        for cl, vertex in self.__cliques_finished:
            if not cl.isdisjoint(clnew) and vertex in clnew:
                # print "reject ", clnew, vnew, " because of ", cl, vertex
                return True
        if autoAdd:
            self.__cliques_finished.append([set(clnew), vnew])
        return False

    def addReplay(self, bag, parent_bag_required=tuple(), weight=1.0):
        assert (len(set(bag).intersection(parent_bag_required)) == 0)
        assert (len(bag) == 1)  # required for next assert, not necessarily required in general tough
        assert (len(set(parent_bag_required).intersection(b[0] for _, b, _ in self.__replay)) == 0)
        if self.__replay is None:
            return
        # print parent_bag_required, bag
        # if parent_bag_required not in self.__replay:
        #    self.__replay[parent_bag_required] = []
        self.__replay.append((parent_bag_required, bag, weight))
        return True

    ######[0]######
    # used for removing degree 0 and 1 vertices
    def remove_hyper_degree_vertex(self, d_up_to=1, log_deg0_replay=True):
        return self._remove_degree_vertex(lambda: self.__hgp.hyper_degree_iter(), d_up_to=d_up_to,
                                          log_deg0_replay=log_deg0_replay)

    ######[]######
    # used for removing degree 0 and 1 vertices
    def remove_degree_vertex(self, d_up_to=1, log_deg0_replay=True):
        return self._remove_degree_vertex(lambda: self.__hgp.degree_iter(), d_up_to=d_up_to,
                                          log_deg0_replay=log_deg0_replay)

    def _remove_degree_vertex(self, iter, d_up_to=1, log_deg0_replay=True):
        dl = []
        for n, dd, ngbs in iter():  # note that iter is potentially lazy
            if dd <= d_up_to:
                dl.append((n, ngbs, dd))
        # self.__hgp.remove_nodes_from(dl) #obsolete
        pos = 0
        for n, ngbs, dd in dl:
            del self.__hgp[n]
            pos += 1
            # self.addReplay(n, parent_bag_required=((ni for ni in nb if ni not in map(lambda x: x[0], dl[:pos])) for nb in ngbs))
            # print ngbs
            parent_bag = []
            for nb in ngbs.values():
                # print nb
                parent_bag.extend(ni for ni in nb if ni not in map(lambda x: x[0], dl[:pos]))
            if log_deg0_replay or dd > 1:  # otherwise does not make sense for fhtd
                self.addReplay((n,), parent_bag_required=parent_bag, weight=1.0)

        return len(dl) > 0

    ######[1]######
    # for some cases with degree 2 vertices
    # only if lower bound tw \geq 2
    # only works savely, without increasing the fhtw, up to rank 2!
    # otherwise it might increase fhtw by at most one
    def almost_simplicial_hypergraph(self, contract_up_to_rank=2, clique_rank_at_least=3, edge_contr=False):
        if self.__lb < 2 or not edge_contr:  # todo: implement pending operations that fire if lower bound is high enough
            return False
        edge_contr = []
        for n, dd, _ in self.__hgp.hyper_degree_iter():
            if dd == 2:
                adj = tuple(self.__hgp.hg.edge_rank(n))
                assert (len(adj) <= 2)
                ngb_cand = set()
                ngb_edge = None
                edge_cand = None
                for (e, r) in adj:
                    #print(e,r)
                    if r > contract_up_to_rank or e not in map(lambda x: x[0], edge_contr):
                        # either we have a small rank (or both adjacent vertice have and edge_cand to be contracted not set)
                        if r <= contract_up_to_rank and edge_cand is None:
                            edge_cand = e
                            # always keep the other vertex in the graph!
                            n = e if e[0] == n else (e[1], e[0])
                            # edge_cand = [ei for ei in e if ei != n]
                            ngb_cand.update(edge_cand)
                            # edge_cand.append(n)
                            # edge_cand = [n]
                            # edge_cand.extend([ei for ei in e if ei != n])
                        elif r >= clique_rank_at_least:
                            ngb_edge = e  # tuple(ei for ei in e if ei != n)
                            ngb_cand.update(e)

                            # ng_bcand.difference_update((n,))
                if edge_cand is not None and ngb_edge is not None and not self.clique_finished(ngb_edge, n[0]):
                    # TODO: add weight function
                    # edge_contr.append((edge_cand, ngb_cand, ((edge_cand, 1.0), (ngb_edge, 1.0))))
                    edge_contr.append((edge_cand, n[1], ngb_cand, 1.0 + 1.0))
        self.contract(edge_contr)

        return len(edge_contr) > 0

    def contract(self, edge_contr):
        # print edge_contr
        # print self.__hgp.hg.nodes(), self.__hgp.hg.edges(), edge_contr
        repl = {}

        def respect_repl(v):
            return v if v not in repl else repl[v]

        for (e, erepr, ngbs, w) in edge_contr:
            # print e, ngbs, w
            ex = {respect_repl(v) for v in e}
            ngbs = {respect_repl(v) for v in ngbs}
            # new representative
            e = tuple(ex)
            assert (len(e) >= 2)
            # print e, e2, self.__hgp.hg.nodes(), self.__hgp.hg.edges()
            # if len(e) >= 2:
            contr = ex.difference((erepr,))
            ngbs.difference_update(contr)
            logging.debug("contracting {0}: {1}, {2}".format(e, self.__hgp.hg.nodes(), self.__hgp.hg.edges()))
            self.__hgp.hg.contract_edge(e, erepr)
            logging.debug("post-contracting {0}: {1}, {2}".format(e, self.__hgp.hg.nodes(), self.__hgp.hg.edges()))
            self.addReplay(tuple(contr), parent_bag_required=tuple(ngbs), weight=w)
            self.update_finished_cliques(contr, erepr)
            # self.addReplay(e[1:], parent_bag_required=(e[0:1],))
            # print ngbs, e
            for (k, v) in repl.items():
                if v in contr:
                    repl[k] = erepr
            for v in contr:
                repl[v] = erepr
        # print self.__hgp.hg.nodes(), self.__hgp.hg.edges()
        # assert(False)

    def consider_lb(self, new_lb):
        self.__lb = max(self.__lb, new_lb)

    def update_lb(self, cl, maxcl, max_clique=True):
        if max_clique:
            self.consider_lb(maxcl / 2.0)
        elif not self.__hgp.hg.isSubsumed(set(cl)):
            self.consider_lb(self.__hgp.hg.fractional_cover(cl))

    ######[3]###### then maybe [2] again
    # simplicial vertices based on fhe cover, which is polynomial time computable
    def simplicial_primalgraph(self, clique_prevent_he_at_least=3, clique_prevent_he_up_to=3):
        # print clique_prevent_he_up_to, clique_prevent_he_at_least
        assert (3 <= clique_prevent_he_at_least <= clique_prevent_he_up_to)
        dl = []
        for (simpl, cl, (kmax, maxcl)) in self.__hgp.simplicial_iter(0, clique_prevent_he_at_least,
                                                                     clique_prevent_he_up_to):
            # print simpl
            # immediately do the thing for the clique
            self.update_lb(cl, maxcl, kmax == 3)
            # print(cl)
            assert (len(cl) == 0 or len(cl) >= 2)
            for (k, s) in simpl:
                # print k, s
                assert (s == 0)
                dl.append((k, cl, maxcl / 2 if kmax <= 3 else 0))
        pos = 1
        for e, cl, fhec in dl:
            if fhec == 0:  # kmax > 3
                # TODO: weight function
                fhec = self.__hgp.hg.fractional_cover(self.__hgp.neighbors(e, False))  # solution=sol)
                self.consider_lb(fhec)
            assert (fhec >= 1)
            cl = set(cl)
            # there could be double occurrences
            if e in self.__hgp.nodes():
                del self.__hgp[e]
                cl.remove(e)
                assert (len(cl) >= 1)
                cl.difference_update((e for e, _, _ in dl[:pos]))
                self.addReplay((e,), parent_bag_required=cl, weight=fhec)  # TODO: weight function
            # print edge_contr
            pos += 1
        return len(dl) > 0

    def almost_simplicial_primalgraph(self, simplicial_diff=1, clique_prevent_he_at_least=3, clique_prevent_he_up_to=3,
                                      edge_contr=False):
        assert (clique_prevent_he_up_to >= clique_prevent_he_at_least >= 3)
        edge_contr = [] if edge_contr else None
        for (simpl, cl, (kmax, maxcl)) in self.__hgp.simplicial_iter(simplicial_diff, clique_prevent_he_at_least,
                                                                     clique_prevent_he_up_to):
            # print cl, kmax
            # immediately do the thing for the clique
            self.update_lb(cl, maxcl, kmax == 3)
            for (k, s) in simpl:
                # print "SIMPL, ", cl, k, s
                fhec = self.__hgp.hg.fractional_cover(self.__hgp.neighbors(k, False))

                # print k,s,fhec
                assert (0 < s <= simplicial_diff)
                # todo: pending operations
                if edge_contr is not None and self.__lb >= fhec + 1:
                    if 1 == s <= simplicial_diff:
                        # assert(self.__lb > 1)
                        # print fhec + 1, self.__lb
                        # print self.__lb, fhec + 1
                        ngbs = set(self.__hgp.neighbors(k))
                        assert (k not in ngbs)
                        assert (len(ngbs.difference(cl)) == 1)
                        contr = (ngbs.difference(cl).pop(), k)
                        if not self.clique_finished(cl, contr[0]):
                            # print ngb, k, ngbs
                            # print ngb
                            m = list(map(lambda x: x[0], edge_contr))
                            if contr not in m and (contr[1], contr[0]) not in m:
                                edge_contr.append((contr, k, ngbs, fhec + 1))  # TODO: weight function
                            # self.__hgp.hg.contract_edge([k, ngbs[0]])
                    else:
                        raise NotImplementedError()
                self.consider_lb(fhec)

        # print "meat"
        if edge_contr is not None:
            self.contract(edge_contr)
            return len(edge_contr) > 0
        else:
            return False

    # todo: find something to increase the lower bound, are there known values for cliques,
    # todo  where no three vertices are contained in one hyperedge (only two) [might be binary edges as well, special case]

    # do something with hyperedge circles?

    # do something where we exploit (up to 13 nodes :P) that fhtw = max(fhtw(N[v]), fhtw(G-v)) where fruitful..
