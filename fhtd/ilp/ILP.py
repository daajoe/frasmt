import argparse
import os
import sys

import time
from HTD import *
import networkx as nx


def read_hyper_graph(fname):
    with open(fname, 'r') as solution_file:
        l3 = solution_file.readline()
        l3 = l3.replace('p edge', '')
        l3 = l3.replace('\n', '')
        l3 = l3.split()
        temp_nv = int(l3[0])
        ed = list()
        temp_ne = int(l3[1])
        for i1 in range(1, temp_ne + 1):
            l3 = solution_file.readline()
            if l3[0]!='e':
                break
            # print l3,
            l3 = l3.replace('e ', '')
            l3 = l3.split()
            temp_ed = list()
            for i in l3:
                temp_ed.append(int(i) - 1)
            ed.append(temp_ed)
            # temp_og.add_edge(int(l3[0]), int(l3[1]))
        if len(ed)!=temp_ne:
            print "edges missing:",temp_ne,len(ed)
    return ed, temp_nv


def parse_args():
    parser = argparse.ArgumentParser(description='%s -f instance')
    parser.add_argument('-f', '--file', dest='instance', action='store', type=lambda x: os.path.realpath(x),
                        help='instance', required=True)
    parser.add_argument('-a', '--solver-args', dest='solver_args', action='store', type=str,
                        help='solver_args', default='')
    parser.add_argument('-w', '--solver-wall-clock-limit', dest='timelimit', action='store', type=int,
                        help='time-limit',
                        default=900)
    parser.add_argument('--runid', dest='runid', action='store', type=int, help='id of the current repeation',
                        default=1)
    parser.add_argument('-b', '--bfs-budget', dest='budget', action='store', type=int, help='bfs budget',
                        default=10)
    parser.add_argument('-r', '--subsolver-budget', dest='subsolver_budget', action='store', type=int,
                        help='subsolver retry budget',
                        default=10)
    args = parser.parse_args()
    if not os.path.isfile(args.instance):
        sys.stderr.write('File "%s" does not exist.\n' % args.instance)
        exit(16)
    return args


def main():
    args = parse_args()
    fname = args.instance
    timeout = args.timelimit
    path = os.path.dirname(fname)
    solver_args = args.solver_args
    runid = args.runid
    subsolver_budget = args.subsolver_budget
    budget = args.budget
    os.chdir(path)
    ed, nv = read_hyper_graph(fname)
    ne = len(ed)
    print ed
    g=nx.Graph()
    g.add_edges_from(ed)

    wallstart = time.time()
    err = ''

    wallstart = time.time()
    ip=fhtd(g)
    ip.make_prob(g)
    wall = time.time() - wallstart


if __name__ == "__main__":
    main()
