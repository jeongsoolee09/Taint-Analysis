from pomegranate import DiscreteDistribution, BayesianNetwork, Node, ConditionalProbabilityTable
import time
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
import csv
import networkx as nx
import itertools as it
import os
import re

print("starting..")
start = time.time()

edges = pd.read_csv("edges.csv", index_col=0, header=[0, 1])
edge_targets = edges.iloc[:, edges.columns.get_level_values(1) == "name"]

regex = r'\((.*)\)'
regex = re.compile(regex)

raw_data = open("raw_data.csv", "r+")
data_reader = csv.reader(raw_data)

edges_data = open("edges.csv", "r+")
edges_reader = csv.reader(edges_data)


# TODO: Dead 스트링의 끝에 )가 하나 남음
def tuple_string_to_tuple(tuple_string):
    string_list = tuple_string.split(", ")
    string_list[0] = string_list[0].lstrip('(')
    string_list[1] = string_list[1].rstrip(')')
    string_list[1] = string_list[1]+')'
    return (string_list[0], string_list[1])


def parse_chain(var_and_chain):
    var = var_and_chain[0]
    chain = var_and_chain[1]
    chain = chain.split(" -> ")
    chain = list(filter(lambda string: string != "", chain))
    chain = list(map(lambda item: item.lstrip(), chain))
    chain = list(map(lambda string: tuple_string_to_tuple(string), chain))
    return [var, chain]


def create_var_and_chain():
    current_path = os.path.abspath("..")
    chainfile = os.path.join(current_path, "benchmarks", "fabricated",
                             "Chain.txt")
    with open(chainfile, "r+") as chain:
        lines = chain.readlines()
        var_to_chain = list(filter(lambda line: line != "\n", lines))
        var_to_chain = list(map(lambda line: line.rstrip(), var_to_chain))
        var_and_chain = list(map(lambda line: line.split(": "), var_to_chain))
        var_and_chain = list(map(lambda lst: parse_chain(lst), var_and_chain))
    return var_and_chain


def collect_src(chain_without_var):  # priority 4
    out = []
    chain_head = chain_without_var[0]
    if "Define" in chain_head[1]:  # sanity check
        activity = chain_head[1]
        callee_methname = activity.split("using")[1]
        callee_methname = callee_methname.lstrip(" ")
        out.append(callee_methname)
    return out


def collect_san(chain_without_var):  # priority 3
    out = []
    for (meth, activity) in chain_without_var:
        if "Redefine" in activity:
            out.append(meth)
    return out


def collect_sin(chain_without_var):  # priority 2
    out = []
    chain_end = chain_without_var[len(chain_without_var)-1]
    if "Dead" in chain_end[1]:
        out.append(chain_end[0])
    return out


def collect_non(chain_without_var, src_s, san_s, sin_s, setofallmethods):
    # priority 1
    src_s = set(src_s)
    san_s = set(san_s)
    sin_s = set(sin_s)
    setofallmethods = set(setofallmethods)
    non_suspects = list(setofallmethods - src_s - san_s - sin_s)
    return non_suspects


flatPrior = DiscreteDistribution({'src': 0.25, 'sin': 0.25,
                                  'san': 0.25, 'non': 0.25})


def df_reader():
    with open("df.txt", "r+") as df:
        lines = df.readlines()
        lines = list(map(lambda line: line.rstrip(), lines))
        lines = list(map(lambda line: line.split(", "), lines))
        lines = list(map(lambda line: tuple(line), lines))
    return lines


def call_reader():
    with open("callg.txt", "r+") as callg:
        lines = callg.readlines()
        lines = list(map(lambda line: line.rstrip(), lines))
        lines = list(map(lambda line: line.split(", "), lines))
        lines = list(map(lambda line: tuple(line), lines))
    return lines


df_edges = df_reader()
call_edges = call_reader()


# Methods for Graphs ================================


def add_node_to_graph(G):
    """creates a graph for identifying root nodes"""
    next(data_reader)  # Headers don't taste good
    for data in data_reader:
        code = "G.add_node('"+data[6]+"')"
        exec(code, globals(), locals())


def findRoot(G):
    roots = []
    for node in G.nodes:
        if G.in_degree(node) == 0:
            roots.append(node)
    return roots


def add_edge_to_graph(G):
    """adds edges to reference graph G"""
    next(edges_reader)
    next(edges_reader)
    for row in edges_reader:
        pkg1 = row[2]
        rtntype1 = row[3]
        name1 = row[4]
        intype1 = "()" if row[5] == "void" else "("+row[5]+")"
        pkg2 = row[7]
        rtntype2 = row[8]
        name2 = row[9]
        intype2 = "()" if row[10] == "void" else "("+row[10]+")"
        firstNodeID = rtntype1+" "+pkg1+"."+name1+intype1
        secondNodeID = rtntype2+" "+pkg2+"."+name2+intype2
        G.add_edge(firstNodeID, secondNodeID)


def find_edges_of(node):
    global graph_for_reference
    lookup_edges = graph_for_reference.edges
    out = []
    for (m1, m2) in lookup_edges:
        if m2 == node:
            out.append((m1, m2))
    return out


def decide_edgekind(node):
    """하나의 node를 받아 그 node가 속한 모든 엣지의 각 종류(df, call, sim)를 판별한다."""
    edges = find_edges_of(node)
    out = []
    for edge in edges:
        if edge in df_edges:
            out.append((edge, "df"))
        elif edge in call_edges:
            out.append((edge, "call"))
        else:
            out.append((edge, "sim"))
    return out


def init_graph():
    """Initialize a (directed acyclic) graph for reference."""
    G = nx.DiGraph()
    add_node_to_graph(G)
    add_edge_to_graph(G)
    return G


# ====================================================
# Methods for BNs ====================================


def create_roots_for_BN(G, BN):
    """identifies roots nodes from G and adds them to BN"""
    counter = 0
    for root in findRoot(G):
        code1 = "s"+str(counter)+" = Node(flatPrior, name=\""+root+"\")"
        exec(code1, globals(), locals())
        code2 = "BN.add_state("+"s"+str(counter)+")"
        exec(code2, globals(), locals())
        counter += 1


def create_raw_CPTs_for_BN(G, BN):
    root = set(findRoot(G))
    internal_leaves = set(G.nodes)-root
    labels = [1, 2, 3, 4]       # src, sin, san, non
    raw_cpts = []
    for node in internal_leaves:
        print(node)
        edgekinds = decide_edgekind(node)
        print(edgekinds)
        cond_prob_table_width = len(list(G.predecessors(node)))
        cond_prob_table_gen = it.repeat(labels, cond_prob_table_width+1)
        cond_prob_table = list(cond_prob_table_gen)
        cond_prob_table = it.product(*cond_prob_table)
        cond_prob_table = it.chain.from_iterable(cond_prob_table)
        temp = np.fromiter(cond_prob_table, int).reshape(-1, cond_prob_table_width+1)
        print(temp)
        raw_cpts.append(temp)
    return raw_cpts
        
    # cond_prob_table = ConditionalProbabilityTable(cond_prob_table, G.predecessors(node))


def add_edge_to_BN(BN):
    pass


def init_BN():
    global graph_for_reference
    BN = BayesianNetwork("Automatic Inference of Taint Method Specifications")
    create_roots_for_BN(graph_for_reference, BN)
    # create_internal_leaves_for_BN(graph_for_reference, BN)
    # add_edge_to_BN(BN)
    return BN


# ====================================================
graph_for_reference = init_graph()
BN_for_inference = init_BN()


# should be called AFTER graph_for_reference is constructed
def create_tactics(chain_without_var):
    """consuming a chain in tuple list form,
    plans ahead how to question the oracle"""
    setofallmethods = graph_for_reference.nodes()
    src_suspects = collect_src(chain_without_var)  # priority 4
    san_suspects = collect_san(chain_without_var)  # priority 3
    sin_suspects = collect_sin(chain_without_var)  # priority 2
    non_suspects = collect_non(chain_without_var, src_suspects, san_suspects,
                               sin_suspects, setofallmethods)  # priority 1
    return {"src": src_suspects, "san": san_suspects,
            "sin": sin_suspects, "non": non_suspects}


var_and_chain = create_var_and_chain()
tactics_per_var = list(map(lambda x: (x[0], create_tactics(x[1])),
                           var_and_chain))

default_df_probs_16 = [
    0.1, 0.3, 0.3, 0.3,
    0.2, 0.2, 0.2, 0.4,
    0.2, 0.3, 0.2, 0.3,
    0.2, 0.2, 0.2, 0.4
]


default_df_probs_64 = [
    0.4, 0.2, 0.2, 0.2,
    0.2, 0.4, 0.2, 0.2,
    0.2, 0.2, 0.4, 0.2,
    0.2, 0.2, 0.2, 0.4,
    0.4, 0.2, 0.2, 0.2,
    0.2, 0.4, 0.2, 0.2,
    0.2, 0.2, 0.4, 0.2,
    0.2, 0.2, 0.2, 0.4,
    0.4, 0.2, 0.2, 0.2,
    0.2, 0.4, 0.2, 0.2,
    0.2, 0.2, 0.4, 0.2,
    0.2, 0.2, 0.2, 0.4,
    0.4, 0.2, 0.2, 0.2,
    0.2, 0.4, 0.2, 0.2,
    0.2, 0.2, 0.4, 0.2,
    0.2, 0.2, 0.2, 0.4,
]


labelmap = {"src":1, "sin":2, "san":3, "non":4}


def take_first_four(lst):
    return lst[0:4]


def take_second_four(lst):
    return lst[4:8]


def take_third_four(lst):
    return lst[8:12]


def take_fourth_four(lst):
    return lst[12:16]


def adapt_df_probs_to_current(parent_label, child_label):
    parent_label_num = labelmap[parent_label]
    child_label_num = labelmap[child_label]
    ndarrays = create_raw_CPTs_for_BN(graph_for_reference, BN_for_inference)
    for ndarray in ndarrays:
        result = list(zip(*np.where(ndarray == parent_label_num)))
        result = list(filter(lambda tup: tup[1] == 0, result))
        indices = list(map(lambda tup: tup[0], result))
        if len(ndarray) == 16:
            previous_probs_16 = default_df_probs_16[:]
            highest = indices[child_label_num-1]
            indices.remove(highest)
            lowest = indices
            # highest에는 0.7을, lowest에는 0.1을 할당하면 된다.
            previous_probs_16[highest] = 0.7
            for i in lowest:
                previous_probs_16[i] = 0.1
        elif len(ndarray) == 64:
            # highest와 lowest의 정의를 다르게 해야 한다.
            previous_probs_64 = default_df_probs_64[:]
            print(indices)
            if child_label_num == 1:  # src
                highest_rows = take_first_four(indices)
            elif child_label_num == 2:  # sin
                highest_rows = take_second_four(indices)
            elif child_label_num == 3:  # san
                highest_rows = take_third_four(indices)
            elif child_label_num == 4:  # non
                highest_rows = take_fourth_four(indices)
            print(highest_rows)
            highest = highest_rows[child_label_num-1]
            # print(highest)
            highest_rows.remove(highest)
            lowest = highest_rows
            previous_probs_64[highest] = 0.7
            for i in lowest:
                previous_probs_64[i] = 0.1
            print(previous_probs_64)


def adapt_call_probs_to_current(args):
    pass


print("# of nodes: ", len(list(graph_for_reference.nodes())))
print("# of edges: ", len(list(graph_for_reference.edges())))

plt.clf()
nx.draw(graph_for_reference, font_size=8, with_labels=True,
        pos=nx.circular_layout(graph_for_reference))

raw_data.close()
edges_data.close()

print("elapsed time :", time.time() - start)
