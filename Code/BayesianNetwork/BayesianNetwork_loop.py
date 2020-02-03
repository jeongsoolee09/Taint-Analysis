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


def process_nodes():
    """creates a graph for identifying root nodes"""
    G = nx.Graph()
    for data in dataReader:
        if data[6] == "name":
            continue
        code = "G.add_node('"+data[6]+"')"
        exec(code, globals(), locals())
    return G


def itertuplesGenerator():
    yield from edge_targets.itertuples(index=False)


def generateEdgeTuples():
    for edge in edge_targets.itertuples(index=False):
        yield () + (edge[0],) + (edge[1],)

G = process_nodes()

# 엣지 연결하기: ID와 ID를 연결
# ID 만들기: <패키지: 리턴타입 이름(인풋타입)> 여기서 인풋타입==void인 경우 그냥 ()
def addEdge():
    next(edgesReader)
    next(edgesReader)
    for edge in edgesReader:
        firstNodeID = "<"+edge[2]+": "+edge[3]+" "+edge[4]+"()" if edge[5]=="void" else "("+edge[5]+")"+">"
        print(firstNodeID)


print("elapsed time :", time.time() - start)
