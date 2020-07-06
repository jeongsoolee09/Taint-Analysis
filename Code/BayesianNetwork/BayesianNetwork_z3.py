from z3 import ForAll, And, Implies, IntSort, EmptySet, Int, Solver, Sum, Select, Array, ArraySort, Store, StringSort, String, StringVal
from functools import reduce

MAGNITUDE = ["YG", "Y", "G", "W"]
LABELDICT = {1: "src", 2: "sin", 3: "san", 4: "non"}
MAGDICT = {1: "YG", 2: "Y", 3: "G", 4: "W"}


class CellSet:
    def __init__(self, edges):
        """@params edges: The edges shot by parents (string list)
           Initializes the following:
           1. the set of all cells in a CPT
           2. the column constraint: the sum of each column should be 1
           3. the call_sim constraint: what cells should be assigned the highest probability?
           4. the cell_label constraint: the order of labels appearing
           5. the color constraint:"""
        self.edges = edges
        self.cell_set = self.create_CELL(len(edges))
        self.mag_set = self.create_MAG(len(edges))
        self.parents = [("parent_%d" % i) for i in range(1, len(edges)+1)]
        self.child = "child"

        # Summing the probabilities of a column must yield 1
        self.column_CONSTRAINT =\
            ForAll([Int('i')], And(
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

        # If the labels of parents and the child are all identical, color it Yellow or else White
        self.call_sim_CONSTRAINT =\
            None  # TODO

        self.MAG_P1 =\
            ForAll([Int('i'), Int('j')],
                   Implies(Select(Select(self.mag_set, Int('i')), Int('j')) == StringVal("YG"),
                                                 ForAll([Int('a'), Int('b')], Implies(Select(Select(self.mag_set, Int('a')), Int('b')) != StringVal("YG"),
                                                                                      (Select(Select(self.cell_set, Int('a')), Int('b')) <\
                                                                                       Select(Select(self.cell_set, Int('i')), Int('j')))))))

        self.MAG_P2 =\
            ForAll([Int('i'), Int('j')],
                   Implies(Select(Select(self.mag_set, Int('i')), Int('j')) == StringVal("Y"),
                           ForAll([Int('a'), Int('b')], Implies(And(Select(Select(self.mag_set, Int('a')), Int('b')) != StringVal("YG"),
                                                                    Select(Select(self.mag_set, Int('a')), Int('b')) != StringVal("U")),
                                                                Select(Select(self.cell_set, Int('a')), Int('b')) <\
                                                                Select(Select(self.cell_set, Int('i')), Int('j'))))))

        self.MAG_P3 =\
            ForAll([Int('i'), Int('j')],
                   Implies(Select(Select(self.mag_set, Int('i')), Int('j')) == StringVal("G"),
                                         ForAll([Int('a'), Int('b')], And(Implies(Select(Select(self.mag_set, Int('a')), Int('b')) == StringVal("W"),
                                                                                  Select(Select(self.cell_set, Int('a')), Int('b')) <\
                                                                                  Select(Select(self.cell_set, Int('i')), Int('j'))),
                                                                          Implies(Select(Select(self.cell_set, Int('a')), Int('b')) <\
                                                                                  Select(Select(self.cell_set, Int('i')), Int('j')),
                                                                                  Select(Select(self.mag_set, Int('a')), Int('b')) == StringVal("W"))))))

        self.MAG_P4 =\
            ForAll([Int('i'), Int('j')],
                   Implies(Select(Select(self.mag_set, Int('i')), Int('j')) == StringVal("W"),
                           ForAll([Int('a'), Int('b')],
                                  Implies(Select(Select(self.mag_set, Int('a')), Int('b')) != StringVal("W"),
                                          Select(Select(self.cell_set, Int('i')), Int('j')) <\
                                          Select(Select(self.cell_set, Int('a')), Int('b'))))))

        self.MAG_CONSTRAINT = And(self.MAG_P1, self.MAG_P2, self.MAG_P3, self.MAG_P4)
        

    def create_CELL(self, N):
        """create a 2D Array of all cells represented by a 4 * 4**N 2D array."""
        CELL = Array('CELL', IntSort(), ArraySort(IntSort(), IntSort()))
        for i in range(4):
            row = Array('ROW_%d' % i, IntSort(), IntSort())
            for j in range(4**N):
                cell = Int('cell_%d_%d' % (i, j))
                row = Store(row, j, cell)
            Store(CELL, i, row)
        return CELL


    def create_MAG(self, N):
        """create a 2D Array of all cells represented by a 4 * 4**N 2D array."""
        MAG = Array('MAG', IntSort(), ArraySort(IntSort(), StringSort()))
        for i in range(4):
            row = Array('ROW_%d' % i, IntSort(), StringSort())
            for j in range(4**N):
                mag = String('mag_%d_%d' % (i, j))
                row = Store(row, j, mag)
            Store(MAG, i, row)
        return MAG


    def summarize_edges(self):
        edges = self.edges
        if "df" in edges and ("call" in edges or "sim" in edges):
            return "df_%d/call_%d" % edges.count("df") % edges.count("call")
        elif "df" in edges:
            return "df"
        else:
            return "call"


    def find_index(self, cell):
        """given a cell, retrieves its (row, column) index"""
        tmplst = [(i, j.index(10)) for i, j in enumerate(self.cell_set) if 10 in j]
        if tmplst == []:  # should not happen..
            return EmptySet(IntSort())
        else:
            return tmplst[0]

# Class CellSet end
# Utility Predicates/Functions

def label_of(self, N):
    """set the label of all parents and child a cell represents, given the cell's index and the total number of parents"""
    out = []
    for parent_count in range(1, N+1):
        parent_label = ((self.row//(4**(N-parent_count))) % 4) + 1
        out.append((parent_count, parent_label))
    child_label = self.column+1
    out.append((N+1, child_label))  # the last pair refers to the child
    return out


def label_identical(self):
    """Returns True if the cell's parents and child have identical labels, False otherwise"""
    node_with_labels = self.labels
    labels = list(map(lambda tup: tup[1], node_with_labels))
    identical = reduce(lambda acc, elem: elem == acc, labels, True)
    return identical

solver = Solver()
solver.add()  # 이 이하는 TODO


def parse_edges_kind(edges_kind):
    df_string = edges_kind.split('/')[0]
    call_string = edges_kind.split('/')[1]
    df_count = int(df_string.split('_')[1])
    call_count = int(call_string.split('_')[1])
    return (df_count, call_count)
    

def get_mag(cellset, edges_kind):
    """@params
    cellset: CellSet object
    edges_kind: summarized edges information by summarize_edges()
    요약된 edges를 보고 Solver s를 사용해 해당 policy에 따라 각 cell의 mag를 정함"""
    global solver
    if "df" in edges_kind and "call" in edges_kind:
        df_count, call_count = parse_edges_kind(edges_kind)
        pass # TODO: The most complicated part!
    elif edges_kind == "df":  # 오직 df만 있는 경우
        pass  # TODO
    else:  # 오직 call혹은 sim만 있는 경우
        solver.add(cellset.column_CONSTRAINT,
                   cellset.prob_CONSTRAINT,
                   cellset.call_sim_CONSTRAINT,
                   cellset.MAG_CONSTRAINT)
