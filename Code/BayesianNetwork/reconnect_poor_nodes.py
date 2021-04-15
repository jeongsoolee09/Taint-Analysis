# a module to be used right after split_underlying_graph

import re
import networkx as nx
import pandas as pd
import os
import random

from split_underlying_graph import decycle
from functools import partial, reduce


DF_EDGES = pd.read_csv("df.csv", index_col=0)[["id1", "id2"]]
CALL_EDGES = pd.read_csv("callg.csv", index_col=0)[["id1", "id2"]]
SIM_EDGES = pd.read_csv("pairwise_sims.csv", index_col=0)[["id1", "id2"]]


class NoSolution():
    def __init__(self, node_name):
        self.node_name = node_name


def find_pickled_graph_names():
    return [f for f in os.listdir('.') if re.match(r'.*_graph_[0-9]+$', f)]


def is_isolated_node(G, node_name):
    return len(G.in_edges(nbunch=node_name)) == 0 and\
           len(G.out_edges(nbunch=node_name)) == 0


def is_rich_node(G, node_name):
    return len(G.in_edges(nbunch=node_name)) > 6


def not_yet_rich(G, node_name):
    return len(G.in_edges(nbunch=node_name)) <= 5


def isolated_nodes(G):
    acc = []
    for node_name in G.nodes:
        if len(G.in_edges(nbunch=node_name)) == 0 and\
           len(G.out_edges(nbunch=node_name)) == 0:
            acc.append(node_name)
    return acc


def rich_nodes(G):
    acc = []
    for node_name in G.nodes:
        if len(G.in_edges(nbunch=node_name)) > 6:
            acc.append(node_name)
    return acc


def collect_poor_nodes(graph):
    filterfunc = partial(is_isolated_node, graph)
    return list(filter(filterfunc, list(graph.nodes)))


def collect_all_poor_nodes(graphs):
    poor_nodes = []
    for graph in graphs:
        poor_nodes += collect_poor_nodes(graph)
    return poor_nodes


def collect_all_nonpoor_nodes(graphs):
    nonpoor_nodes = []
    for graph in graphs:
        # sanity check
        assert len(isolated_nodes(graph)) == 0
        nonpoor_nodes += list(graph.nodes)
    return nonpoor_nodes


def lookup_nodes_single(node, graphs):
    """find a single graph that contain the given node."""
    for graph in graphs:
        if node in graph.nodes:
            return graph


def lookup_nodes(node, graphs):
    """find graphs that contain the given node."""
    acc = []
    for graph in graphs:
        if node in graph.nodes:
            acc.append(graph)
    return acc


def lookup_edges(edge, graphs):
    """find graphs that contain the given edge."""
    acc = []
    for graph in graphs:
        if edge in graph.edges:
            acc.append(graph)
    return acc


def pick_my_rows(node, edge_df):
    return edge_df[(edge_df["id1"] == node) |
                   (edge_df["id2"] == node)]


def pick_random_row(dataframe):
    rand_index = random.randint(0, dataframe.shape[0]-1)
    return dataframe.iloc[rand_index, :]


def get_other_graph(poor_node, edge, graphs):
    g1, g2 = lookup_nodes_single(edge[0], graphs), lookup_nodes_single(edge[1], graphs)
    this_graph = lookup_nodes_single(poor_node, graphs)

    if g1 == g2:
        return g1               # 뭘 리턴하든 상관무
    elif g1 == this_graph:
        return g2
    elif g2 == this_graph:
        return g1


def get_other_node(poor_node, edge):
    if edge[0] == edge[1]:
        return edge[0]
    elif edge[0] == poor_node:
        return edge[1]
    elif edge[1] == poor_node:
        return edge[0]


def no_reflexive(edge_dataframe):
    return edge_dataframe[edge_dataframe["id1"] != edge_dataframe["id2"]]


def all_the_same(coll):
    if len(coll) == 0:
        return True
    else:
        head = coll[0]
        return reduce(lambda acc, elem: elem == head and acc, coll, True)


def reconnect_node(poor_node, graphs):
    my_df_edges = DF_EDGES[(DF_EDGES["id1"] == poor_node) |
                           (DF_EDGES["id2"] == poor_node)]

    my_call_edges = CALL_EDGES[(CALL_EDGES["id1"] == poor_node) |
                               (CALL_EDGES["id2"] == poor_node)]

    my_sim_edges = SIM_EDGES[(SIM_EDGES["id1"] == poor_node) |
                             (SIM_EDGES["id2"] == poor_node)]

    all_edges = no_reflexive(pd.concat([ my_df_edges
                                         , my_call_edges
                                         , my_sim_edges ]))
    if all_edges.empty:
        return NoSolution(poor_node)  # No Success

    homelands = lookup_nodes(poor_node, graphs)

    random_edge = tuple(pick_random_row(all_edges))

    edgedata_acc = []
    for homeland in homelands:
        edgedata = homeland.get_edge_data(*random_edge)
        edgedata_acc.append(edgedata)
    assert all_the_same(edgedata_acc)

    other_graph = get_other_graph(poor_node, random_edge, graphs)
    other_node = get_other_node(poor_node, random_edge)

    while len(other_graph.in_edges(nbunch=other_node)) >= 6:
        random_edge = tuple(pick_random_row(all_edges))
        other_graph = get_other_graph(poor_node, random_edge, graphs)
        other_node = get_other_node(poor_node, random_edge)

    for homeland in homelands:
        homeland.remove_node(poor_node)  # also deletes the accompanying edges

    edgekind = edgedata_acc[0]["kind"]
    other_graph.add_edge(*random_edge, kind=edgekind)

    return True                 # Success


def reconnect_poor_nodes(graphs):
    fails = []
    poor_nodes = collect_all_poor_nodes(graphs)
    for poor_node in poor_nodes:
        result = reconnect_node(poor_node, graphs)
        if result == True:
            continue            # Very good
        else:                   # NaNI?
            assert isinstance(result, NoSolution)
            fails.append(result.node_name)
    return fails


def depickle_graphs(graph_names):
    acc = []
    for graph_name in graph_names:
        graph = nx.read_gpickle(graph_name)
        graph.name = graph_name
        acc.append(graph)
    return acc


def stick_to_some_graph(no_solution_node, graphs):
    least_node_graph = min(graphs, key=lambda graph: len(graph.nodes))
    least_node_graph.add_node(no_solution_node)


def deal_with_leftovers(no_solution_nodes, graphs):
    for no_solution_node in no_solution_nodes:
        stick_to_some_graph(no_solution_node, graphs)


def repickle(graphs):
    for graph in graphs:
        nx.write_gpickle(graph, graph.name)


def verify_result():
    """The total set of nodes should not change after running this script"""
    graph_names = find_pickled_graph_names()
    graphs = depickle_graphs(graph_names)
    mother = nx.read_gpickle("graph_for_reference")
    all_nodes = reduce(lambda acc, graph: acc.union(set(graph.nodes)), graphs, set())
    assert set(all_nodes) == set(mother.nodes)


def main():
    graph_names = find_pickled_graph_names()
    graphs = depickle_graphs(graph_names)
    fails = reconnect_poor_nodes(graphs)
    deal_with_leftovers(fails, graphs)
    repickle(graphs)
    verify_result()


if __name__ == "__main__":
    main()
