#!/usr/bin/env false
from __future__ import absolute_import
from __future__ import print_function

import logging
import os
import sys
import inspect

# TODO: fixme
src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
sys.path.insert(0, os.path.realpath(os.path.join(src_path, '../../..')))

src_path = os.path.realpath(os.path.join(src_path, '../../../lib'))

libs = ['htd_validate']

if src_path not in sys.path:
    for lib in libs:
        sys.path.insert(0, os.path.join(src_path, lib))

import htd_validate.utils.hypergraph
import htd_validate.utils.hypergraph_primalview as hgpv
import htd_validate_tests.tests.utils.validateGraph_testcase as vtd

import fhtd.preprocessing.preprocessing as p
import fhtd as d


class TestFHTDPreprocessor(vtd.ValidateGraphTestCase):
    _gr_classname = htd_validate.Hypergraph.__name__
    _type = "Hypergraph"

    def setUp(self):
        logging.basicConfig(level=logging.INFO)

    def tearDown(self):
        pass

    def solveFile(self, file):
        d.FractionalHypertreeDecomposer(self.loadFile(self.filePath(
            file), fischl_format=True)).solve()

    def testBiconnected(self):
        #return
        hg = self.loadFile(self.filePath("testHG/") + "C13_7.edge")
        self.assertIsNotNone(hg)
        pp = d.FractionalHypertreeDecomposer(hg)
        #pp = p.FractionalHyperTreeDecomposition_Preprocessor(hgpv.HypergraphPrimalView(hg))
        self.assertEquals([set(range(1, 14))],
                          [x for x in pp._pp.hgp.biconnected_components()])

        pp.solve()

        #hg = self.loadFile(self.filePathLocal("../graphs/easy/rand-10-20-10-5-10000-05.xml.hg"), fischl_format=True)
        #self.assertIsNotNone(hg)
        #pp = d.FractionalHypertreeDecomposer(hg)
        #pp.solve()
        #assert(False)
        # with self.assertRaises(AttributeError):
        #    pp.biconnected_components()

        hg = self.loadFile(self.filePath("./hyperbench/cq/imdb-q13a.hg"), fischl_format=True)
        self.assertIsNotNone(hg)
        pp = d.FractionalHypertreeDecomposer(hg)
        #pp = p.FractionalHyperTreeDecomposition_Preprocessor(hgpv.HypergraphPrimalView(hg))
        pp.solve()

        self.solveFile("./hyperbench/cq/tpch-synthetic-q10.hg")
        self.solveFile("./hyperbench/cq/lubm-q14.hg")
        self.solveFile("./hyperbench/cq/deep100-q01.hg")

        # CHANGE TO TEST MORE INSTANCES
        doRealLifeTests = False
        if doRealLifeTests:
            self.mapBenchmarks("./hyperbench/",
                               lambda args: d.FractionalHypertreeDecomposer(
                                   self.loadFile(args["path"], fischl_format=True)).solve(only_fhtw=True))

    def testRemoveHyperDegree(self):
        hg = self.loadFile(self.filePath("testHG/") + "C13_7.edge")
        self.assertIsNotNone(hg)
        self.assertEquals(13, hg.number_of_nodes())
        pp = p.FractionalHyperTreeDecomposition_Preprocessor(hgpv.HypergraphPrimalView(hg))
        pp.remove_hyper_degree_vertex(0)
        self.assertEquals(13, hg.number_of_nodes())
        hg.add_node(99)
        hg.add_node(87)

        self.assertEquals(15, hg.number_of_nodes())
        pp.remove_hyper_degree_vertex(0)
        self.assertEquals(13, hg.number_of_nodes())
        self.assertEquals(13, hg.number_of_edges())
        hg.add_hyperedge((43, 13))
        hg.add_hyperedge((33, 9))
        hg.add_hyperedge((22, 9, 2))
        hg.add_hyperedge((29, 11, 2))
        hg.add_hyperedge((53, 2, 9))
        hg.add_hyperedge((83, 12, 9))
        # print ([x for x in pp.hgp.biconnected_components()])
        rn13 = set(range(1, 14))
        rn13.update([83, 53, 22, 29])
        self.assertEquals([set([43, 13]), set([9, 33]), rn13],
                          # set([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 83, 53, 22, 29])],
                          sorted([x for x in pp.hgp.biconnected_components()]))

        self.assertEquals(19, hg.number_of_edges())
        pp.remove_hyper_degree_vertex(1)
        self.assertEquals(13, hg.number_of_edges())

    def testRemoveDegree(self):
        hg = self.loadFile(self.filePath("testHG/") + "C13_7.edge")
        self.assertIsNotNone(hg)
        self.assertEquals(13, hg.number_of_nodes())
        pp = p.FractionalHyperTreeDecomposition_Preprocessor(hgpv.HypergraphPrimalView(hg))
        pp.remove_degree_vertex(0)
        self.assertEquals(13, hg.number_of_nodes())
        hg.add_node(99)
        hg.add_node(87)

        self.assertEquals(15, hg.number_of_nodes())
        pp.remove_degree_vertex(0)
        self.assertEquals(13, hg.number_of_nodes())
        self.assertEquals(13, hg.number_of_edges())
        hg.add_hyperedge((43, 13))
        hg.add_hyperedge((33, 9))
        hg.add_hyperedge((22, 9, 2))
        hg.add_hyperedge((29, 11, 2))
        hg.add_hyperedge((53, 2, 9))
        hg.add_hyperedge((83, 12, 9))
        # print ([x for x in pp.hgp.biconnected_components()])
        rn13 = set(range(1, 14))
        rn13.update([83, 53, 22, 29])
        self.assertEquals([set([43, 13]), set([9, 33]), rn13],
                          # set([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 83, 53, 22, 29])],
                          sorted([x for x in pp.hgp.biconnected_components()]))

        self.assertEquals(19, hg.number_of_edges())
        pp.remove_degree_vertex(1)
        self.assertEquals(17, hg.number_of_edges())

    def testTwinVertices(self):
        hg = self.loadFile(self.filePath("testHG/") + "C13_7.edge")
        self.assertIsNotNone(hg)
        self.assertEquals(13, hg.number_of_nodes())
        pp = d.FractionalHypertreeDecomposer(hg)
        pp.twin_vertices()
        self.assertEquals([list(range(1, 14))],
                          # [[1], [2], [3], [4], [5], [6], [7], [8], [9], [10], [11], [12], [13]],
                          sorted(x for x in pp._pp.hgp.iter_twin_vertices()))

    def testAlmostSimplicialHypergraph(self):
        hg = self.loadFile(self.filePath("testHG/") + "C4+.edge")
        self.assertIsNotNone(hg)
        pp = p.FractionalHyperTreeDecomposition_Preprocessor(hgpv.HypergraphPrimalView(hg))
        self.assertEquals(1, pp.lb)
        self.assertEquals(5, len(pp.hgp))
        self.assertEquals(2, len(pp.hgp.hg.edges()))
        print(pp.hgp.hg.edges())

        print(pp.lb)
        self.assertFalse(pp.almost_simplicial_hypergraph(edge_contr=True))
        pp.slb(2)
        print(pp.lb)
        self.assertTrue(pp.almost_simplicial_hypergraph(edge_contr=True))
        self.assertEquals(4, len(pp.hgp))
        self.assertEquals(1, len(pp.hgp.hg.edges()))
        self.assertEquals(list(pp.hgp.hg.edges().values()[0]), list(pp.hgp.hg.nodes_iter()))

        self.assertFalse(pp.almost_simplicial_hypergraph(edge_contr=True))
        self.assertEquals(4, len(pp.hgp))
        self.assertEquals(1, len(pp.hgp.hg.edges()))
        self.assertEquals(list(pp.hgp.hg.edges().values()[0]), list(pp.hgp.hg.nodes_iter()))
        print(pp.hgp.hg.edges())

    def testAlmostSimplicialPrimal(self):
        hg = self.loadFile(self.filePath("testHG/") + "C13_7.edge")
        self.assertIsNotNone(hg)
        pp = p.FractionalHyperTreeDecomposition_Preprocessor(hgpv.HypergraphPrimalView(hg))
        self.assertEquals(1, pp.lb)
        self.assertEquals(13, len(pp.hgp))
        # print hg.largest_clique_asp(ground=False)
        # assert(False)
        pp.simplicial_primalgraph()
        self.assertGreaterEqual(pp.lb, 1.5)
        self.assertEquals(13, len(pp.hgp))
        pp.almost_simplicial_primalgraph(edge_contr=True)
        self.assertEquals(13, len(pp.hgp))
        print(pp.lb)
        pp.simplicial_primalgraph()
        pp.almost_simplicial_primalgraph(clique_prevent_he_up_to=9, edge_contr=True)
        self.assertEquals(13, len(pp.hgp))
        # self.assertGreaterEqual(pp.lb, 1.75)
        self.assertGreaterEqual(pp.lb, 1.85)
        print(pp.lb)

    def filePathLocal(self, file):
        return os.path.join(os.path.dirname(__file__), file)

    def testAlmostSimplicialPrimal2(self):
        hg = self.loadFile(self.filePath("testHG/") + "C4+.edge")
        self.assertIsNotNone(hg)
        print(hg.largest_clique_asp(ground=False, prevent_k_hyperedge=5))
        # assert(False)
        pp = p.FractionalHyperTreeDecomposition_Preprocessor(hgpv.HypergraphPrimalView(hg))
        self.assertEquals(1, pp.lb)
        self.assertEquals(5, len(pp.hgp))
        self.assertEquals(2, len(pp.hgp.hg.edges()))
        print(pp.hgp.hg.edges())
        # print list(pp.hgp.hg.nodes_iter())

        pp.slb(3.0)
        self.assertTrue(pp.almost_simplicial_primalgraph(1, clique_prevent_he_up_to=5, edge_contr=True))
        print(pp.hgp.hg.edges())
        print(pp.hgp.nodes())
        self.assertEquals(4, len(pp.hgp.nodes()))
        self.assertEquals(1, len(pp.hgp.hg.edges()))

        self.assertTrue(pp.simplicial_primalgraph(clique_prevent_he_up_to=5))
        self.assertEquals(0, len(pp.hgp))
        self.assertEquals(0, len(pp.hgp.hg.edges()))

        # self.assertTrue(pp.almost_simplicial_primalgraph(1, clique_sizes_at_least=2, edge_contr=True))
        # self.assertEquals(0, len(pp.hgp))
        # self.assertEquals(0, len(pp.hgp.hg.edges()))
        # print pp.hgp.hg.edges()

        hg = self.loadFile(self.filePath("testHG/") + "C4+.edge")
        self.assertIsNotNone(hg)
        pp = p.FractionalHyperTreeDecomposition_Preprocessor(hgpv.HypergraphPrimalView(hg))
        pp.slb(2)

        # print pp.hgp.hg.edges()
        self.assertTrue(pp.simplicial_primalgraph(clique_prevent_he_up_to=5))
        self.assertEquals(2, len(pp.hgp))
        self.assertEquals(1, len(pp.hgp.hg.edges()))
        self.assertEquals(list(tuple(pp.hgp.hg.edges().values())[0]), list(pp.hgp.hg.nodes()))

        hg = self.loadFile(self.filePath("testHG/") + "C4+.edge")
        self.assertIsNotNone(hg)
        pp = p.FractionalHyperTreeDecomposition_Preprocessor(hgpv.HypergraphPrimalView(hg))
        pp.slb(2.99)
        # print "used lwb:", pp.lb
        # assert(False)

        self.assertFalse(pp.almost_simplicial_primalgraph(clique_prevent_he_up_to=5, edge_contr=True))
        self.assertEquals(5, len(pp.hgp))
        self.assertEquals(2, len(pp.hgp.hg.edges()))

        hg = self.loadFile(self.filePath("./hyperbench/cq/imdb-q10b.hg"), fischl_format=True)
        print("Hg:")
        print(hg)
        print("nodes:")
        print(hg.nodes())
        print(hg.edges())
        hgp = hgpv.HypergraphPrimalView(
            self.loadFile(self.filePath("./hyperbench/cq/imdb-q10b.hg"), fischl_format=True))

        pp = p.FractionalHyperTreeDecomposition_Preprocessor(hgp)

        pp.preprocess()

        print(hgp.nodes())
        print(hgp.edges())
        # self.assertFalse(True)
        aset = hg.largest_clique_asp(timeout=2, enum=True, ground=False)
        # self.assertTrue(False)
        # self.maxCliqueFromFile(mx, self.filePath(""), fischl_format=True)

        hgp = hgpv.HypergraphPrimalView(
            self.loadFile(self.filePath("./hyperbench/cq/imdb-q13a.hg"), fischl_format=True))

        pp = p.FractionalHyperTreeDecomposition_Preprocessor(hgp)
        print(pp.preprocess())

        print(hgp.nodes())
        print(hgp.hg.edges())

        doRealLifeTests = False
        if doRealLifeTests:
            self.mapBenchmarks("./hyperbench/",
                               lambda args: print(p.FractionalHyperTreeDecomposition_Preprocessor(hgpv.HypergraphPrimalView(
                                   self.loadFile(args["path"], fischl_format=True))).preprocess()))
