# 현재 문제:
# 1. 메모리가 터짐

from pomegranate import DiscreteDistribution, BayesianNetwork
import time
import random
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
import csv
import networkx as nx
import itertools as it

print("starting..")
start = time.time()

edges = pd.read_csv("edges.csv", index_col=0, header=[0, 1])
edge_targets = edges.iloc[:, edges.columns.get_level_values(1) == "name"]

raw_data = open("raw_data.csv", "r+")
dataReader = csv.reader(raw_data)
edges_data = open("edges.csv", "r+")
edgesReader = csv.reader(edges_data)

flatPrior = DiscreteDistribution({'src': 0.25, 'sin': 0.25,
                                  'san': 0.25, 'non': 0.25})


# Methods for Graphs ================================


def addNodeToGraph(G):
    """creates a graph for identifying root nodes"""
    next(dataReader)  # Headers don't taste good
    for data in dataReader:
        code = "G.add_node('"+data[6]+"')"
        exec(code, globals(), locals())


def findRoot(G):
    roots = []
    for node in G.nodes:
        if G.in_degree(node) == 0:
            roots.append(node)
    return roots


def addEdgeToGraph(G):
    """adds edges to reference graph G"""
    next(edgesReader)
    next(edgesReader)
    for row in edgesReader:
        intype1 = "()" if row[5] == "void" else "("+row[5]+")"
        intype2 = "()" if row[10] == "void" else "("+row[10]+")"
        firstNodeID = "<"+row[2]+": "+row[3]+" "+row[4] + intype1 + ">"
        secondNodeID = "<"+row[7]+": "+row[8]+" "+row[9] + intype2 + ">"
        G.add_edge(firstNodeID, secondNodeID)
        # code = "G.add_edge(firstNodeID, secondNodeID)"
        # exec(code, globals(), locals())


def initGraph():
    """Initialize a (directed acyclic) graph for reference."""
    G = nx.DiGraph()
    addNodeToGraph(G)
    addEdgeToGraph(G)
    return G


# ====================================================
# Methods for BNs ====================================


def createRootsForBN(G, BN):
    """identifies roots nodes from G and adds them to BN"""
    counter = 0
    for root in findRoot(G):
        code1 = "s"+str(counter)+" = Node(flatPrior, name=\""+root+"\")"
        exec(code1, globals(), locals())
        code2 = "BN.add_state("+"s"+str(counter)+")"
        exec(code2, globals(), locals())
        counter += 1


def createInternalLeavesForBN(G, BN):
    root = set(findRoot(G))
    internalLeaves = set(G.nodes)-root
    labels = [1, 2, 3, 4]
    for node in internalLeaves:
        condProbTableWidth = len(list(G.predecessors(node)))
        condProbTableGen = it.repeat(labels, condProbTableWidth)
        condProbTable = list(condProbTableGen)
        condProbTable = it.product(*condProbTable)
        condProbTable = it.chain.from_iterable(condProbTable)
        temp = np.fromiter(condProbTable, int).reshape(-1, condProbTableWidth)
    # condProbTable = ConditionalProbabilityTable(condProbTable, G.predecessors(node))


def addEdgeToBN(BN):
    pass


def initBN():
    global graphForReference
    BN = BayesianNetwork("Automatic Inference of Taint Method Specifications")
    createRootsForBN(graphForReference, BN)
    createInternalLeavesForBN(graphForReference, BN)
    # addEdgeToBN(BN)
    return BN


# ====================================================


graphForReference = initGraph()
# BaysianNetwork = initBN()

print("# of nodes: ", len(list(graphForReference.nodes())))
print("# of edges: ", len(list(graphForReference.edges())))

# nx.draw_circular(graphForReference, font_size=8)
# plt.figure(3,figsize=(12,12))
# plt.tight_layout()
# plt.savefig("Graph.png", format="PNG")
# plt.show()

print("elapsed time :", time.time() - start)
