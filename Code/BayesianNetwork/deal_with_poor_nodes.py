# import modin.pandas as pd
import pandas as pd
import networkx as nx
import glob

import pickle                   # TEMP

from split_underlying_graph import decycle
from functools import partial, update_wrapper
from pandarallel import pandarallel
from itertools import product


pandarallel.initialize()


def find_poor_node_files():
    return glob.glob("*_poor")


# Constants ========================================
# ==================================================


DF_EDGES = pd.read_csv("df.csv", index_col=0)
CALL_EDGES = pd.read_csv("callg.csv", index_col=0)
SIM_EDGES = pd.read_csv("pairwise_sims.csv", index_col=0)


# Methods ==========================================
# ==================================================


def create_graph_without_edges(poor_nodes):
    g = nx.DiGraph()
    poor_graph = nx.read_gpickle(poor_nodes)
    for poor_node_name in poor_graph.nodes:
        g.add_node(poor_node_name)
    return g


def add_df_edges(G):
    """Given a graph G whose edge set E is empty, add DF edges to the nodes of G."""
    nodes_df = pd.DataFrame(G.nodes)

    # Warning: SQL Magic ahead!

    # The Cartesian Product.
    carpro = nodes_df.merge(nodes_df, how="cross")
    carpro.columns = ["id1", "id2"]

    # perform a left-join
    left_join = pd.merge(carpro, DF_EDGES, on=["id1", "id2"], how="left", indicator="exists?")

    # only select "id1", "id2", and "exists?"
    projected = left_join.filter(["id1", "id2", "exists?"])

    # only select the rows which exists in both DF_EDGES and carpro
    selected = projected[projected["exists?"] == "both"]

    # drop the column from sample_nodes_df
    selected = selected.drop(columns=["exists?"])

    raw_dicts = selected.to_dict('records')

    tuples = list(map(lambda dict_: tuple(dict_.values()), raw_dicts))
    tuples = list(filter(lambda tup: tup[0] != tup[1], tuples))

    for tuple_ in tuples:
        G.add_edge(*tuple_, kind="df")

    return G


def add_call_edges(G):
    """Given a graph G whose edge set E is empty, add Call edges to the nodes of G."""
    nodes_df = pd.DataFrame(G.nodes)

    # Warning: SQL Magic ahead!

    # The Cartesian Product.
    carpro = nodes_df.merge(nodes_df, how="cross")
    carpro.columns = ["id1", "id2"]

    # perform a left-join
    left_join = pd.merge(carpro, CALL_EDGES, on=["id1", "id2"], how="left", indicator="exists?")

    # only select "id1", "id2", and "exists?"
    projected = left_join.filter(["id1", "id2", "exists?"])

    # only select the rows which exists in both CALL_EDGES and carpro
    selected = projected[projected["exists?"] == "both"]

    # drop the column from sample_nodes_df
    selected = selected.drop(columns=["exists?"])

    raw_dicts = selected.to_dict('records')

    tuples = list(map(lambda dict_: tuple(dict_.values()), raw_dicts))
    tuples = list(filter(lambda tup: tup[0] != tup[1], tuples))

    for tuple_ in tuples:
        G.add_edge(*tuple_, kind="call")

    return G


def add_sim_edges(G):
    """Given a graph G whose edge set E is empty, add Sim edges to the nodes of G."""
    nodes_df = pd.DataFrame(G.nodes)

    # Warning: SQL Magic ahead!

    # The Cartesian Product.
    carpro = nodes_df.merge(nodes_df, how="cross")
    carpro.columns = ["id1", "id2"]

    # perform a left-join
    left_join = pd.merge(carpro, SIM_EDGES, on=["id1", "id2"], how="left", indicator="exists?")

    # only select "id1", "id2", and "exists?"
    projected = left_join.filter(["id1", "id2", "exists?"])

    # only select the rows which exists in both SIM_EDGES and carpro
    selected = projected[projected["exists?"] == "both"]

    # drop the column from sample_nodes_df
    selected = selected.drop(columns=["exists?"])

    raw_dicts = selected.to_dict('records')

    tuples = list(map(lambda dict_: tuple(dict_.values()), raw_dicts))
    tuples = list(filter(lambda tup: tup[0] != tup[1], tuples))

    for tuple_ in tuples:
        G.add_edge(*tuple_, kind="sim")

    return G


def pairup_elems(lst):
    """[1, 2, 3, 4, 5] |-> [(1, 2), (3, 4), 5]"""
    odd_index_elems = lst[::2]
    even_index_elems = lst[1::2]
    zipped = list(zip(odd_index_elems, even_index_elems))
    if len(lst) % 2 == 1:
        return zipped + [lst[(len(lst)-1)]]
    return zipped


def create_single_graph(input_graph):
    """하나의 poor_node 묶음에 대해 엣지가 모두 연결된 complete graph를 만들어 낸다."""
    input_graph = add_sim_edges(add_call_edges(add_df_edges(input_graph)))

    decycle(input_graph)

    return input_graph


def merge_two_graphs(graph1, graph2):
    G = nx.DiGraph()
    for node_name in graph1.nodes:
        G.add_node(node_name)
    for node_name in graph2.nodes:
        G.add_node(node_name)
    return G


def main():
    print("creating poor graphs")

    print("Loading poor graphs...")
    POOR_NODE_FILES = find_poor_node_files()
    raw_graphs = []
    for poor_node_file in POOR_NODE_FILES:
        G = create_graph_without_edges(poor_node_file)
        raw_graphs.append(G)
    pairedup_graphs = pairup_elems(raw_graphs)
    print("Loading poor graphs...done")

    # print("Merging graph pairs...")
    # merged_graphs = []
    # for elem in pairedup_graphs:
    #     if type(elem) == tuple:  # 두 개를 merge함
    #         G = merge_two_graphs(*elem)
    #         merged_graphs.append(G)
    #     else:                    # merge하지 않음
    #         merged_graphs.append(elem)
    # print("Merging graph pairs...done")

    print("creating recycled graphs...")
    complete_graphs = []
    # for graph in merged_graphs:
    for graph in raw_graphs:
        G = create_single_graph(graph)  # BOTTLENECK
        complete_graphs.append(G)
    print("creating recycled graphs...done")

    # for debugging purposes
    # with open("poor_graphs.bin", "wb+") as f:
    #     pickle.dump(complete_graphs, f)

    return complete_graphs


if __name__ == "__main__":
    main()
