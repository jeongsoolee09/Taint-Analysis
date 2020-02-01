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

# 왜 하는지는 모르겠다만
numpy.random.seed(0)
numpy.set_printoptions(suppress=True)

edges = pd.read_csv("edges.csv", index_col=0, header=[0,1])
edge_targets = edges.iloc[:, edges.columns.get_level_values(1)=="name"]

raw_data = open("raw_data.csv", "r+")
dataReader = csv.reader(raw_data)
edges_data = open("edges.csv", "r+")
edgesReader = csv.reader(edges_data)

# 메소드 이름 겹치는 것 (e.g. 메소드 오버라이딩)은 당장은 상관 안할 것.
def process_nodes():
    """creates a graph for identifying root nodes"""
    G = nx.Graph()
    for data in dataReader:
        if data[4] == "name":
            continue
        code = "G.add_node('"+data[4]+"')"
        exec(code, globals(), locals())
    return G

def itertuplesGenerator():
    yield from edge_targets.itertuples(index=False):

def generateEdgeTuples():
    for edge in edge_targets.itertuples(index=False):
        yield () + (edge[0],) + (edge[1],)

process_nodes()


print("elapsed time :", time.time() - start)
