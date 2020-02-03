from pomegranate import *
import matplotlib.pyplot as plt
import seaborn; seaborn.set_style('whitegrid')
import time
import random
import numpy as np
import pandas as pd
import csv
import networkx as nx

start = time.time()

edges = pd.read_csv("edges.csv", index_col=0, header=[0,1])
edge_targets = edges.iloc[:, edges.columns.get_level_values(1)=="name"]

raw_data = open("raw_data.csv", "r+")
dataReader = csv.reader(raw_data)
edges_data = open("edges.csv", "r+")
edgesReader = csv.reader(edges_data)


def process_nodes(G):
    """creates a graph for identifying root nodes"""
    for data in dataReader:
        if data[6] == "name":
            continue
        code = "G.add_node('"+data[6]+"')"
        exec(code, globals(), locals())


# def itertuplesGenerator():
#     yield from edge_targets.itertuples(index=False)


def generateEdgeTuples():
    for edge in edge_targets.itertuples(index=False):
        yield () + (edge[0],) + (edge[1],)



# 엣지 연결하기: ID와 ID를 연결
def addEdge(G):
    """adds edges to graph G"""
    next(edgesReader) # 헤더 맛없어 퉤
    next(edgesReader) # 헤더 맛없어 퉤
    for row in edgesReader:
        intype1 = "()" if row[5]=="void" else "("+row[5]+")"
        intype2 = "()" if row[10]=="void" else "("+row[10]+")"
        firstNodeID = "<"+row[2]+": "+row[3]+" "+row[4] + intype1 + ">"
        secondNodeID = "<"+row[7]+": "+row[8]+" "+row[9] + intype2 + ">"
        code = "G.add_edge(firstNodeID, secondNodeID)"
        exec(code, globals(), locals())


def findRoot(G):
    roots = []
    for node in G.nodes:
        if G.in_degree(node) == 0:
            roots.append(node)
    return roots
            

def initGraph():
    G = nx.DiGraph()
    process_nodes(G)
    addEdge(G)
    return G
    




print("elapsed time :", time.time() - start)
