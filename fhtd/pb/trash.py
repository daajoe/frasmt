#TODO:


# original_graph = read_graph(stream)
#
# print 'here'
# # print hypergraph.edges()
# graphs = simplify(original_graph)
# treewidth = 0
#
# for g in graphs:
#     if not g.edges():
#         continue
#     g = nx.convert_node_labels_to_integers(g, first_label=1)

#     # exit(1)
#     solver = GraphSatTw(g)
#     treewidth = max(solver.treewidth, treewidth)
#
# print '*' * 80
# print 'overall treewidth = %s' % treewidth


#
# #we use clasp here for the moment
# def on_model(model):
#     print 'model=', model
#
#
# # terminate called after throwing an instance of 'Gringo::GringoError'
# # what():  <on_finish>:1:1: error: error in finish callback:
# #    TypeError: on_finish() takes exactly 2 arguments (1 given)
# # def on_finish(res, canceled):
# #        print res, canceled
#
# def on_finish(res):
#     print 'result=', res

# ctl.add("p", [], '{q}.')
# ctl.ground([("p", [])])




for m in xrange(ubound, 0, -1):
    print 'current m=', m
    # print cards
    # exit(1)
    add_all_at_most(cards, m)
    # exit(1)
    # print 'num_cls', num_cls
    # exit(1)
    # print 'start'
    f = ctl.solve_async()  # on_model, on_finish)
    f.wait(timeout)
    # print 'done'
    print f.get().satisfiable
    if not f.get().satisfiable:
        print 'solution found=',
        print m + 1
        exit(0)

exit(1)

cards = []
for line in sys.stdin.readlines():
    line = line.split()
    if line == []:
        continue
    elif line[0] == 'p':
        # add a new atom
        ats = [backend.add_atom() for _ in xrange(int(line[2]))]
        # add a choice on each atom
        [backend.add_rule(head=[a], body=[], choice=True) for a in ats]
        # we need named atoms
        # chs = [ '{a%i}.' %i for i in xrange(int(line[2]))]
        # print chs
        # ctl.add("p", [], ' '.join(chs))
        # ctl.ground([("p", [])])
        continue
    elif line[-1] == '0':
        line = map(lambda x: -int(x), line[:-1])
        backend.add_rule(head=[], body=line, choice=False)
    elif line[-1].startswith('<='):
        max = int(line[-1][2:])
        line = map(lambda x: (int(x), 1), line[:-1])
        cards.append(line)







# until unsat reduce bound and add additional constraints

def add_at_most(cards, m):
    for card in cards:
        backend.add_weight_rule(head=[], lower=m + 1, body=card, choice=False)


def add_at_least(cards, m):
    for card, i in izip(cards, xrange(len(cards))):
        at = backend.add_atom()
        # nucard = map(lambda x: (-x[0],1), card)
        # print nucard
        # print at
        backend.add_weight_rule(head=[at], lower=m, body=card, choice=False)
        # backend.add_rule(head=[], body=[-at],choice=False)


# add_at_least(cards,5)

for m in xrange(max, 0, -1):
    print 'current m=', m
    add_at_most(cards, m)
    res = ctl.solve()
    if not res.satisfiable:
        print 'solution found=',
        print m + 1
        exit(0)
        # #egdes elimination
        # for i in xrange(1,n+1):
        #     for j in xrange(1,n+1):
        #         if (i==j):
        #             continue
        #         for l in xrange(j+1, n+1):
        #             if (i==l):
        #                 continue
        #             add_clause([-1*arc[i][j], -1*arc[i][l], -1*self.ord[j][l], arc[j][l]])
        #             add_clause([-1*arc[i][j], -1*arc[i][l], self.ord[j][l], arc[l][j]])
        #             #redunant
        #             add_clause([-1*arc[i][j], -1*arc[i][l], arc[j][l], arc[l][j]])

        # #forbid self loops
        # for i in xrange(1, n+1):
        #     add_clause([-1*arc[i][i]])
