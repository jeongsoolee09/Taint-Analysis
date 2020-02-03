from pomegranate import *
import time
import random
import numpy as np
import pandas as pd
import csv
import networkx as nx
from itertools import product

start = time.time()

edges = pd.read_csv("edges.csv", index_col=0, header=[0,1])
edge_targets = edges.iloc[:, edges.columns.get_level_values(1)=="name"]

raw_data = open("raw_data.csv", "r+")
dataReader = csv.reader(raw_data)
edges_data = open("edges.csv", "r+")
edgesReader = csv.reader(edges_data)

flatPrior = DiscreteDistribution({'src':0.25, 'sin':0.25, 'san':0.25, 'non':0.25})

# Methods for Graphs ================================
def addNodeToGraph(G):
    """creates a graph for identifying root nodes"""
    next(dataReader) # 헤더 맛없어 퉤
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
    next(edgesReader) # 헤더 맛없어 퉤
    next(edgesReader) # 헤더 맛없어 퉤
    for row in edgesReader:
        intype1 = "()" if row[5]=="void" else "("+row[5]+")"
        intype2 = "()" if row[10]=="void" else "("+row[10]+")"
        firstNodeID = "<"+row[2]+": "+row[3]+" "+row[4] + intype1 + ">"
        secondNodeID = "<"+row[7]+": "+row[8]+" "+row[9] + intype2 + ">"
        code = "G.add_edge(firstNodeID, secondNodeID)"
        exec(code, globals(), locals())

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

def iterateList(lst, n):
    """Utility function for creating a list of identical lists n times"""
    out = []
    for i in range(n):
        out.append(lst)
    return out

def createInternalLeavesForBN(G, BN):
    root = set(findRoot(G))
    internalLeaves = set(G.nodes)-root
    labels = ["src", "sin", "san", "non"]
    for node in list(internalLeaves):
        # find the number of predecessors for each
        condProbTableWidth = len(list(G.predecessors(node)))
        condProbTable = iterateList(labels, condProbTableWidth)
        


def addEdgeToBN(BN):
    pass

def initBN():
    BN = BayesianNetwork("Automatic Inference of Method Specifications")
    createRootsForBN(graphForReference, BN)
    # createInternalLeavesForBN(BN) # --> 여기서 ConditionalProbabilityTable이 필요
    # addEdgeToBN(BN)
    return BN
# ====================================================

graphForReference = initGraph()
BaysianNetwork = initBN()

print("elapsed time :", time.time() - start)
