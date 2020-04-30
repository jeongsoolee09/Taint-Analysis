from pomegranate import DiscreteDistribution, BayesianNetwork, Node
import time
import random
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
    chain = chain.split(" ->")
    chain = list(filter(lambda string: string != "", chain))
    chain = list(map(lambda item: item.lstrip(), chain))
    chain = list(map(lambda string: tuple_string_to_tuple(string), chain))
    return [var, chain]


current_path = os.path.abspath("..")
chainfile = os.path.join(current_path, "benchmarks", "fabricated", "Chain.txt")
with open(chainfile, "r+") as chain:
    lines = chain.readlines()
    var_to_chain = list(filter(lambda line: line != "\n", lines))
    var_to_chain = list(map(lambda line: line.rstrip(), var_to_chain))
    var_and_chain = list(map(lambda line: line.split(": "), var_to_chain))
    var_and_chain = list(map(lambda lst: parse_chain(lst), var_and_chain))


def create_tactics(chain_without_var):
    """consuming a chain in tuple list form,
    plans ahead how to question the oracle"""
    src_suspects = collect_src(chain_without_var)  # priority 4
    san_suspects = collect_san(chain_without_var)  # priority 3
    sin_suspects = collect_sin(chain_without_var)  # priority 2
    non_suspects = collect_non(chain_without_var)  # priority 1
    return {"src": src_suspects, "san": san_suspects,
            "sin": sin_suspects, "non": non_suspects}


def collect_src(chain_without_var):  # priority 4
    out = []
    chain_head = chain_without_var[0]
    if "Define" in chain_head[1]:  # sanity check
        out.append(chain_head[0])
    return out


def collect_san(chain_without_var):  # priority 3
    out = []
    for (meth, activity) in chain_without_var:
        if "Redefine" in activity:
            out.append(meth)
    return out


def collect_sin(chain_without_var):  # priority 2
    out = []
    chain_end = chain_without_var[len(chain)-1]
    if "Dead" in chain_end[1]:
        out.append(chain_end[0])
    return out


# TODO: Caller-Callee Relation 고려해서 필터링 기준 엄격하게 하기
def collect_non(chain_without_var):  # priority 1
    out = []
    chain_only_calls = list(filter(lambda tup: "Call" in tup[1],
                                   chain_without_var))
    chain_only_calls_procs = list(map(lambda tup: tup[0],
                                      chain_only_calls))
    for proc in chain_only_calls_procs:
        proc_matching_tuples = list(filter(lambda tup: tup[0] == proc,
                                           chain_without_var))
        proc_matching_activities = list(map(lambda tup: tup[1],
                                            proc_matching_tuples))
        proc_matching_activities = list(filter(lambda act:
                                               "Define" in act or
                                               "Redefine" in act or
                                               "Dead" in act,
                                               proc_matching_activities))
        if proc_matching_activities == []:
            out.append(proc)
    return out


flatPrior = DiscreteDistribution({'src': 0.25, 'sin': 0.25,
                                  'san': 0.25, 'non': 0.25})


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
        # code = "G.add_edge(firstNodeID, secondNodeID)"
        # exec(code, globals(), locals())


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


def create_internal_leaves_for_BN(G, BN):
    root = set(findRoot(G))
    internal_leaves = set(G.nodes)-root
    labels = [1, 2, 3, 4]
    for node in internal_leaves:
        cond_prob_table_width = len(list(G.predecessors(node)))
        cond_prob_table_gen = it.repeat(labels, cond_prob_table_width)
        cond_prob_table = list(cond_prob_table_gen)
        cond_prob_table = it.product(*cond_prob_table)
        cond_prob_table = it.chain.from_iterable(cond_prob_table)
        temp = np.fromiter(cond_prob_table, int).reshape(-1, cond_prob_table_width)
    # cond_prob_table = ConditionalProbabilityTable(cond_prob_table, G.predecessors(node))


def add_edge_to_BN(BN):
    pass


def init_BN():
    global graph_for_reference
    BN = BayesianNetwork("Automatic Inference of Taint Method Specifications")
    create_roots_for_BN(graph_for_reference, BN)
    create_internal_leaves_for_BN(graph_for_reference, BN)
    # add_edge_to_BN(BN)
    return BN


# ====================================================


graph_for_reference = init_graph()
BN_for_inference = init_BN()

print("# of nodes: ", len(list(graph_for_reference.nodes())))
print("# of edges: ", len(list(graph_for_reference.edges())))

nx.draw_circular(graph_for_reference, font_size=8, with_labels=True)

raw_data.close()
edges_data.close()

print("elapsed time :", time.time() - start)
