#!/usr/bin/env false
from __future__ import absolute_import

import os
import sys
import inspect
from decimal import Decimal


# TODO: fixme
src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
sys.path.insert(0, os.path.realpath(os.path.join(src_path, '../../..')))

src_path = os.path.realpath(os.path.join(src_path, '../../../lib'))

libs = ['htd_validate']

if src_path not in sys.path:
    for lib in libs:
        sys.path.insert(0, os.path.join(src_path, lib))

from io import StringIO
import htd_validate.utils.hypergraph
import htd_validate.utils.hypergraph_primalview as hgpv
import htd_validate_tests.tests.utils.validateGraph_testcase as vtd

from fhtd import FractionalHypertreeDecomposer
# from fhtd.smt import FractionalHypertreeDecomposition_z3 as FractionalHypertreeDecomposition
from fhtd.smt import FractionalHypertreeDecompositionCommandline as FractionalHypertreeDecomposition


class TestFHTDPreprocessor(vtd.ValidateGraphTestCase):
    _gr_classname = htd_validate.Hypergraph.__name__
    _type = "Hypergraph"

    def setUp(self):
        pass

    def tearDown(self):
        pass

    def testEncoding(self):
        #return
        from os import listdir
        from os.path import isfile, join

        path = os.path.join(os.path.realpath(os.path.dirname(__file__)), "../graphs/")
        files = [f for f in listdir(path) if isfile(join(path, f)) and f.endswith('.hg')]
        for file in files:
            print("INSTANCE %s" % file)
            opt = os.path.splitext(os.path.basename(file))[0]
            exp_width = None
            with open(os.path.join(path, "%s.opt" % opt)) as f:
                exp_width = float(f.readlines()[0])
            fname = os.path.join(path, file)
            hypergraph = htd_validate.Hypergraph.from_file(fname, fischl_format=True)

            stream = StringIO()
            smt_bin = '../lib/z3-4.8.7-x64-ubuntu-16.04/bin/z3'
            smt_bin = '/home/vagrant/src/frasmt/lib/optimathsat/optimathsat-1.6.3'

            # decomposer = FractionalHypertreeDecomposer(hypergraph, timeout=20, stream=stream, checker_epsilon=epsilon,
            #                                            ghtd=False, solver_bin=smt_bin, odebug=None)

            decomposer = FractionalHypertreeDecomposition(hypergraph, timeout=20, stream=stream,
                                                          solver_bin=smt_bin,
                                                          checker_epsilon=None,
                                                          ghtd=False, odebug=None
                                                          )
            res = decomposer.solve()
            width = res['objective']

            self.assertEqual(width, exp_width,
                             "td validation result wrong, should be: %s in: %s" % (width, exp_width))

        pass
