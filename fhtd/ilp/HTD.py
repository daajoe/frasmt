import cplex
# from hyG import *
from itertools import combinations, permutations
import numpy as np
import inspect


class td:
    def __init__(self, graph):
        self.n = graph.number_of_nodes()
        self.m = graph.number_of_edges()
        self.ng = 0
        self.ord = np.zeros((self.n, self.n), dtype=int)
        self.varlist = list()
        self.varlist.append('w')
        self.w = self.ng
        self.ng += 1
        self.nr = 1
        for i in xrange(self.n):
            for j in xrange(self.n):
                if i == j:
                    continue
                self.ord[i][j] = self.ng
                self.ng += 1
                self.varlist.append('o' + str(i) + '_' + str(j))
        self.arc = np.zeros((self.n, self.n), dtype=int)
        for i in xrange(self.n):
            for j in xrange(self.n):
                if i == j:
                    continue
                self.arc[i][j] = self.ng
                self.ng += 1
                self.varlist.append('a' + str(i) + '_' + str(j))

    def first_sum(self, prob):
        rows = list()
        row = list()
        rhs = list()
        senses = list()
        # First sum w>= sum_j(y_{i,j}) for all i
        for i in range(self.n):
            row.append(list())
            names = list()
            formula = list()
            names.append(self.w)
            formula.append(1.0)
            for j in range(self.n):
                if i == j:
                    continue
                names.append(self.arc[i][j])
                formula.append(-1.0)
            row[len(row) - 1].append(names)
            row[len(row) - 1].append(formula)
            rows.append('r_' + str(self.nr))
            self.nr += 1
            rhs.append(0)
            senses.append('hypergraph')
        print(len(row), len(senses), len(rhs), len(rows))
        prob.linear_constraints.add(lin_expr=row, senses=senses, rhs=rhs, names=rows)

    def second_sum(self, prob):
        rows = list()
        row = list()
        rhs = list()
        senses = list()
        # First sum x(i,j)+x(j,i)=1 for all i
        for i in range(self.n):
            for j in range(self.n):
                if i == j:
                    continue
                row.append(list())
                names = list()
                formula = list()
                names.append(self.ord[i][j])
                formula.append(1.0)
                names.append(self.ord[j][i])
                formula.append(1.0)
                row[len(row) - 1].append(names)
                row[len(row) - 1].append(formula)
                rows.append('r_' + str(self.nr))
                self.nr += 1
                rhs.append(1)
                senses.append('E')
        prob.linear_constraints.add(lin_expr=row, senses=senses, rhs=rhs, names=rows)

    def third_sum(self, prob):
        rows = list()
        row = list()
        rhs = list()
        senses = list()
        # First sum x(i,j)+x(j,i)=1 for all i
        for i in range(self.n):
            for j in range(self.n):
                if i == j:
                    continue
                for k in range(self.n):
                    if j == k or i == k:
                        continue
                    row.append(list())
                    names = list()
                    formula = list()
                    names.append(self.ord[i][j])
                    formula.append(1.0)
                    names.append(self.ord[j][k])
                    formula.append(1.0)
                    names.append(self.ord[i][k])
                    formula.append(-1.0)
                    row[len(row) - 1].append(names)
                    row[len(row) - 1].append(formula)
                    rows.append('r_' + str(self.nr))
                    self.nr += 1
                    rhs.append(1)
                    senses.append('L')
        prob.linear_constraints.add(lin_expr=row, senses=senses, rhs=rhs, names=rows)

    def fourth_sum(self, prob):
        rows = list()
        row = list()
        rhs = list()
        senses = list()
        # First sum x(i,j)+x(j,i)=1 for all i
        for i in range(self.n):
            for j in range(self.n):
                if i == j:
                    continue
                row.append(list())
                names = list()
                formula = list()
                names.append(self.arc[i][j])
                formula.append(1.0)
                names.append(self.ord[i][j])
                formula.append(-1.0)
                row[len(row) - 1].append(names)
                row[len(row) - 1].append(formula)
                rows.append('r_' + str(self.nr))
                self.nr += 1
                rhs.append(0)
                senses.append('L')
        prob.linear_constraints.add(lin_expr=row, senses=senses, rhs=rhs, names=rows)

    def fifth_sum(self, prob, graph):
        rows = list()
        row = list()
        rhs = list()
        senses = list()
        # First sum x(i,j)+x(j,i)=1 for all i
        for edge in graph.edges():
            row.append(list())
            names = list()
            formula = list()
            names.append(self.arc[edge[0]][edge[1]])
            formula.append(1.0)
            names.append(self.ord[edge[0]][edge[1]])
            formula.append(-1.0)
            row[len(row) - 1].append(names)
            row[len(row) - 1].append(formula)
            rows.append('r_' + str(self.nr))
            self.nr += 1
            rhs.append(0)
            senses.append('E')
            row.append(list())
            names = list()
            formula = list()
            names.append(self.arc[edge[1]][edge[0]])
            formula.append(1.0)
            names.append(self.ord[edge[1]][edge[0]])
            formula.append(-1.0)
            row[len(row) - 1].append(names)
            row[len(row) - 1].append(formula)
            rows.append('r_' + str(self.nr))
            self.nr += 1
            rhs.append(0)
            senses.append('E')
        prob.linear_constraints.add(lin_expr=row, senses=senses, rhs=rhs, names=rows)

    def sixth_sum(self, prob):
        rows = list()
        row = list()
        rhs = list()
        senses = list()
        # First sum x(i,j)+x(j,i)=1 for all i
        for i in range(self.n):
            for j in range(self.n):
                if i == j:
                    continue
                for k in range(self.n):
                    if i == k or j == k:
                        continue
                    row.append(list())
                    names = list()
                    formula = list()
                    names.append(self.ord[j][k])
                    formula.append(1.0)
                    names.append(self.arc[i][j])
                    formula.append(1.0)
                    names.append(self.arc[i][k])
                    formula.append(-1.0)
                    names.append(self.arc[j][k])
                    formula.append(-1.0)
                    row[len(row) - 1].append(names)
                    row[len(row) - 1].append(formula)
                    rows.append('r_' + str(self.nr))
                    self.nr += 1
                    rhs.append(2)
                    senses.append('L')
        prob.linear_constraints.add(lin_expr=row, senses=senses, rhs=rhs, names=rows)

    def make_vars(self, prob):
        my_ub = []
        my_lb = []
        my_obj = []
        for _ in range(self.ng):
            my_ub.append(1)
            my_lb.append(0)
            my_obj.append(0)
        my_obj[self.w] = 1.0
        my_ub[self.w] = self.ng
        my_lb[self.w] = 0
        types = [prob.variables.type.binary] * self.ng
        types[self.w] = prob.variables.type.integer
        prob.variables.add(obj=my_obj, ub=my_ub, names=self.varlist, types=types, lb=my_lb)

    def make_prob(self, g, time_out=600):
        prob = cplex.Cplex()
        prob.set_error_stream('err.error')
        prob.objective.set_sense(prob.objective.sense.minimize)
        prob.parameters.timelimit.set(time_out)
        self.make_vars(prob)
        # print prob.variables.get_names()
        self.first_sum(prob)
        # print "linear", prob.linear_constraints.get_names()
        self.second_sum(prob)
        self.third_sum(prob)
        self.fourth_sum(prob)
        self.fifth_sum(prob, g)
        self.sixth_sum(prob)
        prob.write('form.lp')
        print("solving")
        print(self.nr, self.ng)
        print(self.varlist)
        try:
            prob.solve()
            print(prob.solution.get_values('w'))
            return prob.solution.get_values('w')
        except Exception as e:
            print(e)
            # print "timeout"
            return False


class flow_network(td):
    def __init__(self, graph):
        td.__init__(self, graph)
        self.flow = np.zeros((self.n, self.n, self.n, self.n), dtype=int)
        for i in graph.nodes():
            for w in graph.nodes():
                if (i, w) in graph.edges():
                    for u in graph.nodes():
                        for v in graph.nodes():
                            if u == v:
                                continue
                            self.flow[u][v][i][w] = self.ng
                            self.ng += 1
                            self.varlist.append('f_' + str(u) + '_' + str(v) + '_' + str(i) + '_' + str(w))
        self.path = np.zeros((self.n, self.n, self.n), dtype=int)
        for i in graph.nodes():
            for u in graph.nodes():
                if i == u:
                    continue
                for v in graph.nodes():
                    if i == v or u == v:
                        continue
                    self.path[u][v][i] = self.ng
                    self.ng += 1
                    self.varlist.append('g_' + str(u) + '_' + str(v) + '_' + str(i))

    def make_vars(self, prob):
        my_ub = []
        my_lb = []
        my_obj = []
        for i in range(self.ng):
            my_ub.append(1)
            my_lb.append(0)
            my_obj.append(0)
        my_obj[self.w] = 1.0
        my_ub[self.w] = self.ng
        my_lb[self.w] = 0
        types = [prob.variables.type.binary] * self.ng
        types[self.w] = prob.variables.type.integer
        print(len(my_obj), len(my_ub), len(self.varlist), len(types), len(my_lb))
        print(self.varlist)
        prob.variables.add(obj=my_obj, ub=my_ub, names=self.varlist, types=types, lb=my_lb)

    def fifteenth_sum(self, prob, graph):
        rows = list()
        row = list()
        rhs = list()
        senses = list()
        # First sum x(i,j)+x(j,i)=1 for all i
        for i in range(self.n):
            for j in range(self.n):
                if i == j:
                    continue
                for k in range(self.n):
                    row.append(list())
                    names = list()
                    formula = list()
                    names.append(self.path[i][j][k])
                    formula.append(1.0)
                    for m in range(self.n):
                        if (k, m) in graph.edges():
                            names.append(self.flow[i][j][m][k])
                            formula.append(-1.0)
                    row[len(row) - 1].append(names)
                    row[len(row) - 1].append(formula)
                    rows.append('r_' + str(self.nr))
                    self.nr += 1
                    rhs.append(0)
                    senses.append('E')
                    print(row)
                prob.linear_constraints.add(lin_expr=row, senses=senses, rhs=rhs, names=rows)

    def make_prob(self, g, time_out=600):
        prob = cplex.Cplex()
        prob.set_error_stream('err.error')
        prob.objective.set_sense(prob.objective.sense.minimize)
        prob.parameters.timelimit.set(time_out)
        self.make_vars(prob)
        # print prob.variables.get_names()
        self.first_sum(prob)
        self.fifteenth_sum(prob, g)
        # print "linear", prob.linear_constraints.get_names()
        # self.second_sum(prob)
        # self.third_sum(prob)
        # self.fourth_sum(prob)
        # self.fifth_sum(prob, g)
        # self.sixth_sum(prob)
        prob.write('form.lp')
        print("solving")
        print(self.nr, self.ng)
        print(self.varlist)
        try:
            prob.solve()
            print(prob.solution.get_values('w'))
            return prob.solution.get_values('w')
        except Exception as e:
            print(e)
            # print "timeout"
            return False


class ghtd(td):
    def __init__(self, graph):
        td.__init__(self, graph)
        self.cov = np.zeros((self.n, self.m), dtype=int)
        for i in xrange(self.n):
            for e in xrange(self.m):
                self.cov[i][e] = self.ng
                self.ng += 1
                self.varlist.append('cov_' + str(i) + '_' + str(e))

    def thirtyfifth_sum(self, prob):
        rows = list()
        row = list()
        rhs = list()
        senses = list()
        # First sum w>= sum_j(y_{i,j}) for all i
        for i in xrange(self.n):
            row.append(list())
            names = list()
            formula = list()
            names.append(self.w)
            formula.append(1.0)
            for j in xrange(self.m):
                names.append(self.cov[i][j])
                formula.append(-1.0)
            row[len(row) - 1].append(names)
            row[len(row) - 1].append(formula)
            rows.append('r_' + str(self.nr))
            self.nr += 1
            rhs.append(0)
            senses.append('hypergraph')
        print(len(row), len(senses), len(rhs), len(rows))
        prob.linear_constraints.add(lin_expr=row, senses=senses, rhs=rhs, names=rows)

    def thirtysixth_sum(self, prob, graph):
        rows = list()
        row = list()
        rhs = list()
        senses = list()
        # First sum w>= sum_j(y_{i,j}) for all i
        for i in xrange(self.n):
            for j in xrange(self.n):
                if i == j:
                    continue
                row.append(list())
                names = list()
                formula = list()
                names.append(self.arc[i][j])
                formula.append(1.0)
                for e in xrange(self.m):
                    if j in graph.edges()[e]:
                        names.append(self.cov[i][e])
                        formula.append(-1.0)
                row[len(row) - 1].append(names)
                row[len(row) - 1].append(formula)
                rows.append('r_' + str(self.nr))
                self.nr += 1
                rhs.append(0)
                senses.append('L')
        print(len(row), len(senses), len(rhs), len(rows))
        # print row
        prob.linear_constraints.add(lin_expr=row, senses=senses, rhs=rhs, names=rows)

    def thirthyseventh_sum(self, prob, graph):
        rows = list()
        row = list()
        rhs = list()
        senses = list()
        # First sum w>= sum_j(y_{i,j}) for all i
        for i in xrange(self.n):
            row.append(list())
            names = list()
            formula = list()
            for e in xrange(self.m):
                if i in graph.edges()[e]:
                    names.append(self.cov[i][e])
                    formula.append(1.0)
            row[len(row) - 1].append(names)
            row[len(row) - 1].append(formula)
            rows.append('r_' + str(self.nr))
            self.nr += 1
            rhs.append(0)
            senses.append('hypergraph')
        print(len(row), len(senses), len(rhs), len(rows))
        # print row
        prob.linear_constraints.add(lin_expr=row, senses=senses, rhs=rhs, names=rows)

    def make_vars(self, prob):
        my_ub = []
        my_lb = []
        my_obj = []
        for i in range(self.ng):
            my_ub.append(1)
            my_lb.append(0)
            my_obj.append(0)
        my_obj[self.w] = 1.0
        my_ub[self.w] = self.ng
        my_lb[self.w] = 0
        types = [prob.variables.type.binary] * self.ng
        types[self.w] = prob.variables.type.integer
        print("*" * 60)
        print(dir(prob.variables.type))
        print("*" * 60)
        print(len(my_obj), len(my_ub), len(self.varlist), len(types), len(my_lb))
        print(self.varlist)
        prob.variables.add(obj=my_obj, ub=my_ub, names=self.varlist, types=types, lb=my_lb)

    def make_prob(self, g, time_out=600):
        prob = cplex.Cplex()
        prob.set_error_stream('err.error')
        prob.objective.set_sense(prob.objective.sense.minimize)
        prob.parameters.timelimit.set(time_out)
        self.make_vars(prob)
        # print prob.variables.get_names()
        # print "linear", prob.linear_constraints.get_names()
        self.second_sum(prob)
        self.third_sum(prob)
        self.fourth_sum(prob)
        self.fifth_sum(prob, g)
        self.sixth_sum(prob)
        self.thirtyfifth_sum(prob)
        self.thirtysixth_sum(prob, g)
        self.thirthyseventh_sum(prob, g)
        prob.write('form.lp')
        print("solving")
        print(self.nr, self.ng)
        print(self.varlist)
        try:
            prob.solve()
            print(prob.solution.get_values('w'))
            return prob.solution.get_values('w')
        except Exception as e:
            print(e)
            # print "timeout"
            return False


class fhtd(ghtd):
    def __init__(self, graph):
        ghtd.__init__(self, graph)

    def make_vars(self, prob):
        my_ub = []
        my_lb = []
        my_obj = []
        for i in range(self.ng):
            my_ub.append(1)
            my_lb.append(0)
            my_obj.append(0)
        my_obj[self.w] = 1.0
        my_ub[self.w] = self.ng
        my_lb[self.w] = 0
        types = [prob.variables.type.binary] * self.ng
        types[self.w] = prob.variables.type.continuous
        for i in xrange(self.n):
            for e in xrange(self.m):
                types[self.cov[i][e]] = prob.variables.type.continuous
        print(len(my_obj), len(my_ub), len(self.varlist), len(types), len(my_lb))
        print(self.varlist)
        prob.variables.add(obj=my_obj, ub=my_ub, names=self.varlist, types=types, lb=my_lb)
