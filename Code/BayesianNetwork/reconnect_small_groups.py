import networkx as nx
import json
import graphviz
import csv
import os
import re
import networkx.algorithms as nxalg

from functools import reduce

from networkx.exception import NetworkXNoCycle
from make_BN import tame_rich
from itertools import product


# Constants ========================================
# ==================================================

def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]

with open(retrieve_path()+"skip_func.txt", "r+") as skip_func:
    skip_funcs = skip_func.readlines()
    skip_funcs = list(map(lambda string: string.rstrip(), skip_funcs))

df_data = open("df.csv", "r+")
df_reader = csv.reader(df_data)

call_data = open("callg.csv", "r+")
call_reader = csv.reader(call_data)

sim_data = open("pairwise_sims.csv", "r+")
sim_reader = csv.reader(sim_data)

def no_reflexive(relation):
    return list(filter(lambda tup: tup[0] != tup[1], relation))

DF_EDGES = no_reflexive(map(lambda lst: (lst[5], lst[10]), list(df_reader)[1:]))
CALL_EDGES = no_reflexive(map(lambda lst: (lst[5], lst[10]), list(call_reader)[1:]))
SIM_EDGES = no_reflexive(map(lambda lst: (lst[5], lst[10]), list(sim_reader)[1:]))

MAX_GROUP_SIZE = 6


# Functionalities ==================================
# ==================================================

def find_pickled_graph_names():
    return [f for f in os.listdir('.') if re.match(r'.*_graph_[0-9]+$', f)]


def identify_small_groups(nx_graph):
    new = nx_graph.to_undirected()
    groups = nx.connected_components(new)  # list of node sets

    return list(filter(lambda chunk: len(chunk) <= MAX_GROUP_SIZE, groups))


def connect(node, nx_graph):
    """주어진 노드들을 nx_graph의 노드들과 연결해 준다.
       주의할 점: 1. rich node가 생기면 안 됨
                2. cycle이 생기면 안 됨"""
    # {node}와 nx_graph.nodes 의 cartesian product
    carpro1 = list(product([node], list(nx_graph.nodes)))
    applicables = []

    for tup in carpro1:
        if tup in DF_EDGES:
            applicables.append((tup, "df"))
        if tup in CALL_EDGES:
            applicables.append((tup, "call"))
        if tup in SIM_EDGES:
            applicables.append((tup, "sim"))

    for (node, other), edgekind in applicables:
        edge = (node, other)
        if len(nx_graph.in_edges(nbunch=other)) >= 6:  # the other node is already rich
            continue
        else:                   # we might be able to add this edge: now test if there is a cycle
            nx_graph.add_edge(*edge, kind=edgekind)
            try:
                nx.find_cycle(nx_graph)
                nx_graph.remove_edge(*edge)  # this will only run if there IS a cycle
            except NetworkXNoCycle:  # we're good to go
                pass

    carpro2 = list(product(list(nx_graph.nodes), [node]))
    applicables = []

    for tup in carpro2:
        if tup in DF_EDGES:
            applicables.append((tup, "df"))
        if tup in CALL_EDGES:
            applicables.append((tup, "call"))
        if tup in SIM_EDGES:
            applicables.append((tup, "sim"))

    for (other, node), edgekind in applicables:
        edge = (other, node)
        if len(nx_graph.in_edges(nbunch=node)) >= 6:  # the other node is already rich
            continue
        else:                   # we might be able to add this edge: now test if there is a cycle
            nx_graph.add_edge(*edge, kind=edgekind)
            try:
                nx.find_cycle(nx_graph)
                nx_graph.remove_edge(*edge)  # this will only run if there IS a cycle
            except NetworkXNoCycle:  # we're good to go
                pass


def reconnect(group, nx_graph):
    """주어진 노드들을 nx_graph의 노드들과 연결해 준다."""
    for node in group:
        connect(node, nx_graph)


def reconnect_small_groups(nx_graph):
    small_groups = identify_small_groups(nx_graph)
    print(small_groups)
    for group in small_groups:
        reconnect(group, nx_graph)


def visualize_graph(nx_graph, filename):
    """visualize as graphviz dot"""
    dot_graph = graphviz.Digraph()
    list(map(lambda node: dot_graph.node(node), list(nx_graph.nodes)))
    list(map(lambda edge: (edgekind := nx_graph.get_edge_data(*edge)["kind"]) and\
             (color := "red" if edgekind == "df" else\
              "black" if edgekind == "call" else "blue") and\
             dot_graph.edge(*edge, color=color), list(nx_graph.edges)))
    dot_graph.render(filename=filename,
                     format="pdf",
                     view=False,
                     quiet=True,
                     cleanup=True)


# Main =============================================
# ==================================================


def main():
    graph_names = find_pickled_graph_names()

    for graph_name in graph_names:
        nx_graph = nx.read_gpickle(graph_name)
        reconnect_small_groups(nx_graph)
        tame_rich(nx_graph)     # do we need this?
        visualize_graph(nx_graph, f"{graph_name}_reconnect_small_groups")

        # repickle!
        nx.write_gpickle(nx_graph, graph_name)


if __name__ == "__main__":
    main()
