import modin.pandas as pd
import networkx as nx
import glob

from split_underlying_graph import decycle
from functools import partial, update_wrapper


def find_poor_node_files():
    return glob.glob("*_poor")


# Constants ========================================
# ==================================================


DF_EDGES = pd.read_csv("df.csv", index_col=0)
CALL_EDGES = pd.read_csv("callg.csv", index_col=0)
SIM_EDGES = pd.read_csv("sim.csv", index_col=0)


# Methods ==========================================
# ==================================================


def create_graph_without_edges(poor_nodes):
    g = nx.DiGraph()
    poor_graph = nx.read_gpickle(poor_nodes)
    for poor_node_name in poor_graph.nodes:
        g.add_node(poor_node_name)
    return g


def add_df_edges(G):
    mapfunc = lambda row: row['id1'] in G.nodes and row['id2'] in G.nodes

    # making original dataframe manageable by dropping irrelevant rows and columns
    small_df_edges = DF_EDGES[['id1', 'id2']]
    bool_df = small_df_edges.apply(mapfunc, axis=1)
    small_df_edges['leave'] = bool_df
    small_df_edges = small_df_edges[small_df_edges.leave != False]

    # adding edges row by row
    for rowtuple in small_df_edges.itertuples(index=False):
        G.add_edge(rowtuple[0], rowtuple[1])  # id1, id2 respectively


def add_call_edges(G):
    mapfunc = lambda row: row['id1'] in G.nodes and row['id2'] in G.nodes

    # making original dataframe manageable
    small_call_edges = CALL_EDGES[['id1', 'id2']]
    bool_df = small_call_edges.apply(mapfunc, axis=1)
    small_call_edges['leave'] = bool_df
    small_call_edges = small_call_edges[small_call_edges.leave != False]

    # adding edges row by row
    for rowtuple in small_call_edges.itertuples(index=False):
        G.add_edge(rowtuple[0], rowtuple[1])  # id1, id2 respectively


def no_symmetric(dataframe):
    dataframe['temp'] = dataframe.index * 2
    dataframe2 = dataframe.iloc[:, [4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 10]]
    dataframe2.columns = dataframe.columns
    dataframe2['temp'] = dataframe2.index * 2 + 1
    out = pd.concat([dataframe, dataframe2])
    out = out.sort_values(by='temp')
    out = out.set_index('temp')
    out = out.drop_duplicates()
    out = out[out.index % 2 == 0]
    out = out.reset_index().drop(columns=['temp'])
    return out


def no_reflexive(dataframe):
    cond1 = dataframe['class1'] != dataframe['class2']
    cond2 = dataframe['rtntype1'] != dataframe['rtntype2']
    cond3 = dataframe['name1'] != dataframe['name2']
    cond4 = dataframe['intype1'] != dataframe['intype2']
    return dataframe[cond1 | cond2 | cond3 | cond4]


def add_sim_edges(G):
    mapfunc = lambda row: row['id1'] in G.nodes and row['id2'] in G.nodes

    print("adding sim_edges...")

    # making dataframe non-reflexive and non-symmetric
    SIM_EDGES_pandas = SIM_EDGES._to_pandas()
    sim_edges_new = no_symmetric(SIM_EDGES_pandas)
    sim_edges_new = no_reflexive(sim_edges_new)

    # making original dataframe manageable
    small_sim_edges = sim_edges_new[['id1', 'id2']]
    bool_df = small_sim_edges.apply(mapfunc, axis=1)
    small_sim_edges['leave'] = bool_df
    small_sim_edges = small_sim_edges[small_sim_edges.leave != False]

    if len(G.nodes) < len(small_sim_edges.index):
        small_sim_edges = small_sim_edges.sample(n=len(G.nodes))

    # adding edges row by row
    # print(len(small_sim_edges.index))
    for rowtuple in small_sim_edges.itertuples(index=False):
        G.add_edge(rowtuple[0], rowtuple[1])  # id1, id2 respectively


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
    add_df_edges(input_graph)
    add_call_edges(input_graph)
    # add_sim_edges(input_graph)

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

    print("Merging graph pairs...")
    merged_graphs = []
    for elem in pairedup_graphs:
        if type(elem) == tuple:  # 두 개를 merge함
            G = merge_two_graphs(*elem)
            merged_graphs.append(G)
        else:                    # merge하지 않음
            merged_graphs.append(elem)
    print("Merging graph pairs...done")

    print("creating recycled graphs...")
    complete_graphs = []
    for graph in merged_graphs:
        G = create_single_graph(graph)  # BOTTLENECK
        complete_graphs.append(G)
    print("creating recycled graphs...done")

    return complete_graphs
