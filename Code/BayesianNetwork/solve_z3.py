# 잘 가 내 코드야...ㅠㅠ

import time
from z3 import *
from basic_CPT import make_call_sim_CPT, make_df_CPT, make_call_df_CPT 
import numpy as np

MAGNITUDE = ["YG", "Y", "G", "W"]
LABELDICT = {1: "src", 2: "sin", 3: "san", 4: "non"}
MAGDICT = {1: "YG", 2: "Y", 3: "G", 4: "W"}


class CPT:
    def __init__(self, edges):
        """@params edges: The edges shot by parents (string list)
           Initializes the following:
           1. the set of all cells in a CPT: cell_set (*Z3 array object*)
           2. the column constraint: the sum of each column should be 1
           3. the probability constraint: all cells are in [0, 100]
           4. the mag constraint: W < G < Y < YG"""
        self.edges = edges  # to reduce boilerplate
        self.solver = Solver()
        self.cell_set = self.create_cell_set()
        self.mag_set = self.create_mag_set()

        # Summing the probabilities of a column must yield 1
        self.column_CONSTRAINT =\
            ForAll([Int('i')], Implies(
                And(0 <= Int('i'), Int('i') < 4**len(edges)),
                Sum(Select(self.cell_set[0], Int('i')),
                    Select(self.cell_set[1], Int('i')),
                    Select(self.cell_set[2], Int('i')),
                    Select(self.cell_set[3], Int('i')))==100))

        # Interpret {0..99} to probs {0.00..0.99}
        self.prob_CONSTRAINT =\
             ForAll([Int('i'), Int('j')],
                    And(0 <= Select(Select(self.cell_set, Int('i')), Int('j')), 
                        Select(Select(self.cell_set, Int('i')), Int('j')) <= 100))

        self.MAG_P1 =\
            ForAll([Int('i'), Int('j')],
                   Implies(Select(Select(self.mag_set, Int('i')), Int('j')) == IntVal(1),
                                                 ForAll([Int('a'), Int('b')], Implies(Select(Select(self.mag_set, Int('a')), Int('b')) != IntVal(1),
                                                                                      (Select(Select(self.cell_set, Int('a')), Int('b')) <\
                                                                                       Select(Select(self.cell_set, Int('i')), Int('j')))))))

        self.MAG_P2 =\
            ForAll([Int('i'), Int('j')],
                   Implies(Select(Select(self.mag_set, Int('i')), Int('j')) == IntVal(2),
                           ForAll([Int('a'), Int('b')], Implies(And(Select(Select(self.mag_set, Int('a')), Int('b')) != IntVal(1),
                                                                    Select(Select(self.mag_set, Int('a')), Int('b')) != IntVal(2)),
                                                                Select(Select(self.cell_set, Int('a')), Int('b')) <\
                                                                Select(Select(self.cell_set, Int('i')), Int('j'))))))

        self.MAG_P3 =\
            ForAll([Int('i'), Int('j')],
                   Implies(Select(Select(self.mag_set, Int('i')), Int('j')) == IntVal(3),
                                         ForAll([Int('a'), Int('b')],
                                             Implies(Select(Select(self.mag_set, Int('a')), Int('b')) == IntVal(4),
                                                                                  Select(Select(self.cell_set, Int('a')), Int('b')) <\
                                                                                  Select(Select(self.cell_set, Int('i')), Int('j'))))))

        self.MAG_P4 =\
            ForAll([Int('i'), Int('j')],
                   Implies(Select(Select(self.mag_set, Int('i')), Int('j')) == IntVal(4),
                           ForAll([Int('a'), Int('b')],
                                  Implies(Select(Select(self.mag_set, Int('a')), Int('b')) != IntVal(4),
                                          Select(Select(self.cell_set, Int('i')), Int('j')) <\
                                          Select(Select(self.cell_set, Int('a')), Int('b'))))))

        self.MAG_CONSTRAINT = And(self.MAG_P1, self.MAG_P2, self.MAG_P3, self.MAG_P4)


    def create_mag_set(self):
        """converts a 2d numpy array (mag set) in to a Z3 array object."""
        N = len(self.edges)
        mag_set = Array('mag_set', IntSort(), ArraySort(IntSort(), IntSort()))
        if "df" in self.edges and "call" in self.edges:
            ndarray = make_call_df_CPT(self.edges)
        elif "df" in self.edges:
            ndarray = make_df_CPT(len(self.edges))
        else:
            ndarray = make_call_sim_CPT(len(self.edges))
        print(ndarray)
        for i in range(4):
            row = Array('ROW_%d' % i, IntSort(), IntSort())
            for j in range(4**N):
                value = int(ndarray[i, j])
                # row = Store(row, j, IntVal(value))
                self.solver.add(Select(Select(mag_set, i), j) == value)
            # Store(mag_set, i, row)
        return mag_set


    def create_cell_set(self):
        """creates a Z3 array object (cell set) to contain probability variables"""
        N = len(self.edges)
        cell_set = Array('cell_set', IntSort(), ArraySort(IntSort(), IntSort()))
        for i in range(4):
            row = Array('ROW_%d' % i, IntSort(), IntSort())
            for j in range(4**N):
                cell = Int('cell_%d_%d' % (i, j))
                row = Store(row, j, cell)
            Store(cell_set, i, row)
        return cell_set


    # provides the main solving functionality
    def solve(self):
        self.solver.add(self.column_CONSTRAINT,
                        self.prob_CONSTRAINT,
                        self.MAG_CONSTRAINT)
        if self.solver.check() == sat:
            print(self.solver.check())
            print(self.solver.model())
            return self.solver.model()
        elif self.solver.check() == unsat:
            print(self.solver.check())
        else:  # should never happen..
            print(self.solver.check())


    # loop 모듈에서 갖다 쓰게 될 함수
    def convert_model_to_2darr(self, model):
        N = len(self.edges)
        arr = np.zeros((4, 4**N)).astype(int)
        for i in range(4):
            for j in range(4**N):
                evaled = model.evaluate(self.cell_set[i][j]).as_long()
                arr[i, j] = evaled
        return arr
        

    # self.mag_set 프린팅해보기
    def debug_mag_set(self, model):
        print(model)
        N = len(self.edges)
        arr = np.zeros((4, 4**N)).astype(int)
        for i in range(4):
            for j in range(4**N):
                evaled = model.evaluate(self.mag_set[i][j]).as_long()
                arr[i, j] = evaled
        return arr


print("starting..")
start = time.time()

a = CPT(["call"])
b = a.solve()
print(a.convert_model_to_2darr(b))
print(a.debug_mag_set(b))

print("elapsed time :", time.time() - start)
