import pandas as pd
import networkx as nx
import glob

import pickle                   # TEMP

from split_underlying_graph import decycle
from functools import partial, update_wrapper
from pandarallel import pandarallel
from itertools import product

import make_underlying_graph
import split_underlying_graph


def find_poor_node_files():
    return glob.glob("*_poor")


def create_graph_without_edges(poor_nodes):
    g = nx.DiGraph()
    for poor_node in poor_nodes:
        g.add_node(poor_node)
    return g


def main():
    POOR_NODE_FILES = find_poor_node_files()
    nodes = []
    for poor_node_file in POOR_NODE_FILES:
        G = nx.read_gpickle(poor_node_file)
        nodes += list(G.nodes)

    edgeless_graph = create_graph_without_edges(nodes)

    mother_graph = make_underlying_graph.parameterized_main(edgeless_graph)
    splitted_graphs = split_underlying_graph.parameterized_main(mother_graph)

    return splitted_graphs
