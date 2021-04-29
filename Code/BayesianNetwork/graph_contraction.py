import networkx as nx
import json
import graphviz
import copy
import csv

from functools import reduce
from make_BN import tame_rich


# Constants ========================================
# ==================================================


call_data = open("callg.csv", "r+")
call_reader = csv.reader(call_data)

def no_reflexive(relation):
    return list(filter(lambda tup: tup[0] != tup[1], relation))

CALL_EDGES = no_reflexive(map(lambda lst: (lst[5], lst[10]), list(call_reader)[1:]))


def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]


with open(retrieve_path()+"skip_func.txt", "r+") as skip_func:
    skip_funcs = skip_func.readlines()
    skip_funcs = list(map(lambda string: string.rstrip(), skip_funcs))


# Functionalities ==================================
# ==================================================


# counter for fresh supernode names
cnt = 0


def identify_chunks(nx_graph):
    # a chunk is a set of a caller and its callees
    new1 = nx.DiGraph()

    # add only the call-edges to new1
    list(map(lambda edge: new1.add_edge(*edge),
             [edge for edge in list(nx_graph.edges)\
              if edge in CALL_EDGES\
              and edge[0] not in skip_funcs and edge[1] not in skip_funcs]))

    new2 = new1.to_undirected()
    chunks = nx.connected_components(new2)  # list of node sets
    return chunks


def lookup_by_pred(pred, pred_edges_data):
    pass


def lookup_by_succ(succ, succ_edges_data):
    pass


def aggregate_caller_callee(nx_graph, chunks):
    global cnt
    new = copy.deepcopy(nx_graph)
    for chunk in chunks:
        # time to do our work!
        # 1. collect the immed. preds
        # 2. collect the immed. succs
        # 3. swap the set of nodes connected with a call-edge with a supernode
        # 4. connect the supernode with the preds
        # 5. connect the supernode with the succs
        chunk_nodes_and_preds = reduce(lambda acc, node: acc+[(node, list(nx_graph.predecessors(node)))],
                                       chunk, [])
        pred_edges = reduce(lambda acc, pair: acc+[(pred, pair[0]) for pred in pair[1]],
                            chunk_nodes_and_preds, [])
        pred_edges_data = dict(reduce(lambda acc, edge: acc+[(edge, nx_graph.get_edge_data(*edge))],
                                      pred_edges, []))
        chunk_nodes_and_succs = reduce(lambda acc, node: acc+[(node, list(nx_graph.successors(node)))],
                                       chunk, [])
        succ_edges = reduce(lambda acc, pair: acc+[(pair[0], succ) for succ in pair[1]],
                            chunk_nodes_and_succs, [])
        succ_edges_data = dict(reduce(lambda acc, edge: acc+[(edge, nx_graph.get_edge_data(*edge))],
                                      succ_edges, []))
        list(map(lambda node: new.remove_node(node), chunk))
        supernode = f"supernode_{cnt}"; cnt += 1

        list(map(lambda pred: new.add_edge(pred, supernode,
                                           kind=pred_edges_data[(pred, supernode)]), preds))
        list(map(lambda succ: new.add_edge(supernode, succ,
                                           kind=succ_edges_data[(supernode, succ)]), succs))

    return new


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
    nx_graph = nx.read_gpickle("Decision-1.1.0_graph_0")
    tame_rich(nx_graph)

    print(f"Number of nodes (before): {nx_graph.number_of_nodes()}")

    # before
    visualize_graph(nx_graph, "graph_0_before")

    chunks = identify_chunks(nx_graph)
    aggregated = aggregate_caller_callee(nx_graph, chunks)
    print(f"Number of nodes (before): {aggregated.number_of_nodes()}")

    # after
    visualize_graph(aggregated, "graph_0_after")
    print("done!")


if __name__ == "__main__":
    main()
