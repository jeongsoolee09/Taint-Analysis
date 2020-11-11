import modin.pandas as pd
import networkx as nx
import csv
import glob

from split_underlying_graph import decycle
from functools import partial
from create_edge import no_symmetric, no_reflexive

def find_poor_node_files():
    return glob.glob("*_poor")

# Constants ========================================
# ==================================================

POOR_NODE_FILES = find_poor_node_files()
DF_EDGES = pd.read_csv("df.csv", index_col=0)
CALL_EDGES = pd.read_csv("callg.csv", index_col=0)
SIM_EDGES = pd.read_csv("sim.csv", index_col=0)

# Methods ==========================================
# ==================================================

def create_graph_without_edges(poor_nodes):
    g = nx.DiGraph()
    for poor_node_name in poor_nodes:
        g.add_node(poor_node_name)
    return g


def raw_mapfunc(poor_nodes, row):
    return row['id1'] in poor_nodes and\
        row['id2'] in poor_nodes


def create_mapfunc(poor_nodes):
    return partial(raw_mapfunc, poor_nodes)


def add_df_edges(G, poor_nodes):
    mapfunc = create_mapfunc(poor_nodes)

    # making original dataframe manageable by dropping irrelevant rows and columns
    small_df_edges = DF_EDGES[['id1', 'id2']]
    bool_df = small_df_edges.apply(mapfunc, axis=1)
    small_df_edges['leave'] = bool_df
    small_df_edges = small_df_edges[small_df_edges.leave != False]

    # adding edges row by row
    for rowtuple in small_df_edges.itertuples(index=False):
        G.add_edge(rowtuple[0], rowtuple[1])  # id1, id2 respectively


def add_call_edges(G, poor_nodes):
    mapfunc = create_mapfunc(poor_nodes)

    # making original dataframe manageable
    small_call_edges = CALL_EDGES[['id1', 'id2']]
    bool_df = small_call_edges.apply(mapfunc, axis=1)
    small_call_edges['leave'] = bool_df
    small_call_edges = small_call_edges[small_call_edges.leave != False]

    # adding edges row by row
    for rowtuple in small_call_edges.itertuples(index=False):
        G.add_edge(rowtuple[0], rowtuple[1])  # id1, id2 respectively


def add_sim_edges(G, poor_nodes):
    mapfunc = create_mapfunc(poor_nodes)

    # making dataframe non-reflexive and non-symmetric
    sim_edges_new = no_symmetric(SIM_EDGES)
    sim_edges_new = no_reflexive(sim_edges_new)

    # making original dataframe manageable
    small_sim_edges = sim_edges_new[['id1', 'id2']]
    bool_df = small_sim_edges.apply(mapfunc, axis=1)
    small_sim_edges['leave'] = bool_df
    small_sim_edges = small_sim_edges[small_sim_edges.leave != False]

    # adding edges row by row
    for rowtuple in small_sim_edges.itertuples(index=False):
        G.add_edge(rowtuple[0], rowtuple[1])  # id1, id2 respectively


def pairup_elems(lst):
    """[1, 2, 3, 4, 5] |-> [(1, 2), (3, 4), 5]"""
    odd_index_elems = x[::2]
    even_index_elems = x[1::2]
    zipped = list(zip(odd_index_elems, even_index_elems))
    if len(lst) % 2 == 1:
        return zipped + [lst[(len(lst)-1)]]
    return zipped


def create_single_graph(unconnected_graph):
    """하나의 poor_node 묶음에 대해 엣지가 모두 연결된 complete graph를 만들어 낸다."""
    def compose(init_arg1, init_arg2, funclist):
        for func in funclist:
            init_arg1 = func(init_arg1, init_arg2)
        return current_value

    complete_graph = compose(unconnected_graph, poor_nodes,
                             [add_df_edges, add_call_edges, add_sim_edges])
    decycle(complete_graph)
    return complete_graph


def merge_two_graphs(graph1, graph2):
    G = nx.DiGraph()
    for node_name in graph1.nodes:
        G.add_node(node_name)
    for node_name in graph2.nodes:
        G.add_node(node_name)
    return G


def main():
    raw_graphs = []
    for poor_node_file in POOR_NODE_FILES:
        G = create_graph_without_edges(poor_nodes)
        graphs.append(G)
    pairedup_graphs = pairup_elems(graphs)

    merged_graphs = []
    for elem in graphs:
        if type(elem) == tuple:  # 두 개를 merge함
            G = merge_two_graphs(*elem)
            merged_graphs.append(G)
        else:                    # merge하지 않음
            merged_graphs.append(elem)

    complete_graphs = []
    for graph in merged_graphs:
        G = create_single_graph(graph)
        complete_graphs.append(G)

    return complete_graphs
