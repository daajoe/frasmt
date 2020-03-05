#!/usr/bin/false
# !/usr/bin/env python
#
# Copyright 2018
# Johannes K. Fichte, TU Wien, Austria, 2018
# Markus Hecher, TU Wien, Austria, 2018
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
from pathlib import Path
import os

import logging
import time
from decimal import Decimal

from htd_validate.decompositions import fhtd
from htd_validate.utils.hypergraph_primalview import Hypergraph, HypergraphPrimalView

from fhtd.preprocessing import FractionalHyperTreeDecomposition_Preprocessor as Preprocessor
from fhtd.smt import FractionalHypertreeDecompositionCommandline
#from fhtd.smt import FractionalHypertreeDecomposition_z3


class FractionalHypertreeDecomposer:
    # suggested order [1], ..., [k]
    def __init__(self, hypergraph, replay=True, lb=1, timeout=20, stream=None, checker_epsilon=None, ghtd=False,
                 solver_bin=None):

        self.__solver_bin = solver_bin
        if not checker_epsilon:
            checker_epsilon = Decimal(0.001)

        self.__checker_epsilon = checker_epsilon
        self._pp = Preprocessor(HypergraphPrimalView(hypergraph), replay=replay, lb=lb)
        self.timeout = timeout
        self.stream = stream
        self.ghtd = ghtd

    ######[ENCODING]######
    # fix ordering; compute independently for each biconnected component
    # todo: for hypergraph?!
    def solve(self, only_fhtw=False, connect_components=True, accuracy=Hypergraph.ACCURACY * 1000, encode_cliques=True,
              encode_twins=True, clique_k=4, run_preprocessing=True, upper_bound=None, preprocessing_only=False,
              FractionalHypertreeDecomposition=FractionalHypertreeDecompositionCommandline):
        pre_wall = time.time()
        if self.ghtd:
            run_preprocessing = False
            logging.warning("Option ghtd disables preprocessing for now!")

        # only fhtw implies connect components
        if only_fhtw:
            connect_components = False
        assert (not only_fhtw or not connect_components)
        # initially, there should not be degree 0 vertices, otherwise there is something
        # seriously wrong, fhtd not defined for that cases!
        self._pp.remove_hyper_degree_vertex(0, log_deg0_replay=False)
        whole_hgp = self._pp.hgp
        bcs = [self._pp.hgp.induced_graph(b, force_copy=True) for b in self._pp.hgp.biconnected_components()]

        # return preps
        tds = []
        solver_run_id = 1
        ret = {'pre_wall': [], 'enc_wall': 'nan', 'z3_wall': 'nan', 'subsolvers': {}, 'pre_clique_size': [],
               'pre_clique_k': [], 'pre_num_twins': [], 'pre_size_max_twin': [], 'smt_objective': 'nan',
               'pre_clique_type': clique_k}

        if len(bcs) == 0:
            assert (len(self._pp.hgp.hg.edges()) == 0 and len(self._pp.hgp.hg.nodes()) == 0)
        else:
            # for b in self.__hgp.biconnected_components():
            for b in bcs:  # self.__hgp.biconnected_components():
                gcheck = b.hg.copy()  # only needed for checking and linking later
                # print self.__hgp.induced_graph(b)
                self._pp.init(b, replay=self._pp.replay is not None)  # , lb=fhtw)
                logging.info("next component: {0}".format(self._pp.hgp.hg))
                if run_preprocessing:
                    pres = self._pp.preprocess()
                    logging.info("preprocessing details: {0}".format(pres))
                    logging.info(
                        "after preprocessing: {0}, {1}".format(self._pp.hgp.hg.edges(), self._pp.hgp.hg.nodes()))
                revert_nodes, revert_edges = self._pp.hgp.hg.relabel_consecutively()
                logging.info("after relabeling: {0}, {1}".format(self._pp.hgp.hg.edges(), self._pp.hgp.hg.nodes()))

                ftd = None
                if len(self._pp.hgp.hg.edges()) == 0:
                    ftd = fhtd.FractionalHypertreeDecomposition(epsilon=self.__checker_epsilon)
                else:
                    # TAKE CLIQUES HERE
                    clique = None
                    if encode_cliques:
                        logging.info("Compute cliques for encoding.")

                        pre_clique_size = 1
                        clique = None

                        # Values clique_k are overloaded
                        # clique_k = 1 ..largest hyperedge, 2 .. largest_clique (Z3), k>3 k-cliques
                        if clique_k == 1:
                            clique = self._pp.hgp.hg.largest_hyperedge()
                        elif clique_k == 2:
                            clique = self._pp.hgp.hg.largest_clique(timeout=60)
                        else:
                            clique_list = \
                            self._pp.hgp.hg.largest_clique_asp(prevent_k_hyperedge=clique_k, enum=False, timeout=60)[2]
                            if len(clique_list) > 0:
                                clique = clique_list[0]
                            pre_clique_size = len(clique_list)

                        if clique is not None:
                            self._pp.update_lb(clique, len(clique), clique_k == 3)

                        logging.info("Computed Clique follows.")
                        logging.info(clique)
                        ret['pre_clique_size'].append(pre_clique_size)
                        ret['pre_clique_k'].append(clique_k)

                    twin_vertices = None
                    if encode_twins:
                        twin_vertices = list(self._pp.hgp.hg.iter_twin_vertices())
                        pre_twin_vertices = len(twin_vertices)
                        pre_size_max_twin = 0 if len(twin_vertices) == 0 else len(max(twin_vertices))

                        twin_vertices = iter(twin_vertices)

                        ret['pre_num_twins'].append(pre_twin_vertices)
                        ret['pre_size_max_twin'].append(pre_size_max_twin)

                    pre_wall = time.time() - pre_wall
                    ret['pre_wall'].append(pre_wall)

                    if preprocessing_only:
                        continue

                    z3_wall = time.time()
                    decomposer = FractionalHypertreeDecomposition(self._pp.hgp.hg, timeout=self.timeout,
                                                                  checker_epsilon=self.__checker_epsilon,
                                                                  ghtd=self.ghtd, solver_bin=self.__solver_bin)
                    res = decomposer.solve(lbound=self._pp.lb if only_fhtw else 1,
                                           clique=clique, twins=twin_vertices, ubound=upper_bound)
                    ret['subsolvers'][solver_run_id] = {'width': res['objective'].numerator/res['objective'].denominator,
                                                        'width_fractional': {'numerator': res['objective'].numerator,
                                                                             'denominator': res['objective'].denominator},
                                                        'decomposition': res['decomposition'],
                                                        # 'smt_solver_stats': res['smt_solver_stats'],
                                                        'z3_wall': time.time() - z3_wall,
                                                        'enc_wall': res['enc_wall']}
                    solver_run_id += 1
                    logging.info(ret)
                    ftd = res["decomposition"]
                    # print '*'*80
                    # print "objective:", res["objective"]
                    # assert(ftd is not None)
                    logging.info("FTW_COMPONENT {0}".format(res["objective"]))
                    if ftd is not None:
                        self._pp.consider_lb(res["objective"])
                    else:
                        assert only_fhtw
                    logging.info("FTW_POST_COMPONENT {0}".format(res["objective"]))
                    # logging.info(str(output))

                # TODO: replace hg by deep copy of current hg component?
                # print whole_hgp.hg
                if ftd is not None:
                    self._pp.hgp.hg.relabel(revert_nodes, revert_edges, revert=False)
                    logging.info(
                        "after relabeling back: {0}, {1}".format(self._pp.hgp.hg.edges(), self._pp.hgp.hg.nodes()))
                    ftd.relabel(revert_nodes, revert_edges)

                    ftd.set_graph(gcheck)
                    assert (self._pp.replay is not None)
                    ftd.replay(self._pp.replay)
                    logging.info("Graph after replay: {0}\n{1}".format(whole_hgp.hg.edges(), whole_hgp.hg.nodes()))
                    logging.info("TD after replay: {0}\n{1}\n{2}".format(ftd.chi, ftd.T.edges(), ftd.weights))
                    assert (ftd.validate(gcheck))

                    if connect_components:
                        i = len(tds) - 1
                        while i >= 0:
                            # print tds[i].graph.nodes(), tds[i].graph.edges()
                            e, eid = ftd.graph.edge_into(tds[i].graph.nodes(), whole_hgp.hg)
                            if e is not None:
                                # print gcheck.edges(), e
                                logging.info(
                                    "CONNECTING {0}, {1} to {2}, {3}".format(ftd.chi, ftd.T.edges(), tds[i].chi,
                                                                             tds[i].T.edges()))
                                conn = ftd.connect(tds[i], e, eid)
                                logging.info("CONNECTING to {0}: {1}, {2}".format(i, ftd.chi, ftd.T.edges()))
                                assert (conn)
                                del tds[i]
                            i -= 1
                        tds.append(ftd)

            logging.info("FTW {0}".format(self._pp.lb))
            if preprocessing_only:
                ret['objective'] = 'na'
                ret['td'] = 'na'
                return ret

            if connect_components:
                # print "TDs", [i.chi for i in tds]
                # print whole_hgp.hg.edges(), tds[0].chi, tds[0].T.edges()
                logging.info("TDs: {0} ".format([str((t.chi, t.weights, t.T.edges())) + "\n\n" for t in tds]))
                for t in tds[1:]:
                    tds[0].connect(t)
                # assert(not connect_components or len(tds) == 1)
                assert (tds[0].validate(whole_hgp.hg, strict=False))
                # assert that treewidth should be within numeric range! (due to cplex)
                if not self._pp.lb - accuracy <= tds[0].max_bag_size() <= self._pp.lb + accuracy:
                    raise ValueError("connected (combined) fhtw should be {0}, but actually is {1}".format(self._pp.lb,
                                                                                                           tds[
                                                                                                               0].max_bag_size()))
                    # assert (self._pp.lb - accuracy <= tds[0].max_bag_size() <= self._pp.lb + accuracy)

        ret['objective'] = self._pp.lb
        ret['td'] = tds[0] if len(tds) > 0 else None
        return ret

    ######[ENCODING]######
    # fix ordering between twin vertices; twin vertices have same primal neighbourhood
    def twin_vertices(self):
        for ts in self._pp.hgp.hg.iter_twin_vertices():
            # todo: use in the encoding!
            logging.debug(str(ts))

    ######[ENCODING]######
    # todo: largest clique/edge (according to rank) at the end?
    # todo  or is largest clique with largest fractional cover (originating from many hyperedges) better?

    # todo: find something to increase the lower bound, are there known values for cliques,
    # todo  where no three vertices are contained in one hyperedge (only two) [might be binary edges as well, special case]

    # do something with hyperedge circles?

    # do something where we exploit (up to 13 nodes :P) that fhtw = max(fhtw(N[v]), fhtw(G-v)) where fruitful..
