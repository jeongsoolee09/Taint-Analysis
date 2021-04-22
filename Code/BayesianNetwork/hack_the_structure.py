import graphviz
import networkx as nx
import networkx.algorithms as nxalg
import networkx.algorithms.traversal.depth_first_search as dfs
import make_BN
import os
import re
import numpy as np
import json

from functools import reduce

graph_files = [f for f in os.listdir('.') if re.match(r'.*_graph_[0-9]+$', f)]

def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]

PROJECT_ROOT_DIR = retrieve_path()

with open(os.path.join(PROJECT_ROOT_DIR, "skip_func.txt"), "r+") as skip_func:
    skip_funcs = skip_func.readlines()
    skip_funcs = list(map(lambda string: string.rstrip(), skip_funcs))


def depickle_all():
    acc = []
    for graph_file in graph_files:
        graph = nx.read_gpickle(graph_file)
        graph.name = graph_file
        acc.append(graph)
    return acc


def partition(coll, n):
    # input sanity check
    if n > len(coll):
        raise ValueError("The size of a partition is too large!")
    if n < 0:
        raise ValueError("The size of a partition cannot be negative!")

    # trivial case
    if len(coll) == 0:
        return coll

    # nontrivial case
    acc = []
    i = 0; j = n
    for _ in range(len(coll)//n):
        acc.append(coll[i:j])
        i += n; j += n

    # append leftovers
    if len(coll[i:]) != 0:
        acc.append(coll[i:])

    return acc


def print_path(graph_for_reference, from_node):
    """BN 상에서 from_node로부터 to_node까지, update가 일어난 path들을 모두 pretty print."""
    # assert len(rich_nodes(graph_for_reference)) == 0  # 야호! 통과한다. 하지만 혹시 몰라 남겨 놓음

    def inner(path, graph_for_reference):
        """ [1, 2, 4] |-> \"1 --call--> 2 --DF--> 4\" """
        zipped = list(zip(path[:len(path)-1], path[1:]))

        def mapfunc(edge):
            try:
                edgekind_dict = graph_for_reference.get_edge_data(edge[0], edge[1])
                edgekind = edgekind_dict["kind"] # may throw TypeError because edgekind_dict may be None
                return str(edge[0]) + "--" + edgekind + "-->" + str(edge[1])
            except TypeError:
                edgekind_dict = graph_for_reference.get_edge_data(edge[1], edge[0])
                edgekind = edgekind_dict["kind"]
                return str(edge[0]) + "<--" + edgekind + "--" + str(edge[1])

        mapped = list(map(mapfunc, zipped))
        return mapped

    BN_undirected = graph_for_reference.to_undirected()
    paths = list(dfs.dfs_preorder_nodes(BN_undirected, from_node))
    i = 1
    for path in paths:
        print("path"+str(i)+":", inner(path, graph_for_reference))
        i += 1

def make_bicycle_chain(coll):
    all_bust_last = coll[:len(coll)-1]
    all_bust_first = coll[1:]
    return list(zip(all_bust_last, all_bust_first))


def make_subgraph_command(digraph_var_name, partition):
    """flexing my metaprogramming skills"""
    bicycle_chains = make_bicycle_chain(partition)
    command_for_elems = map(lambda tup: f"    s.edge(\"{tup[0]}\", \"{tup[1]}\", style=\"invis\")\n", bicycle_chains)
    all_commands = reduce(lambda a, e: a+e, command_for_elems)
    return f"""with {digraph_var_name}.subgraph() as s:
    s.attr(rank="same")
"""+all_commands


def all_same_length(ndlist):
    if type(ndlist[0]) != list:
        return False
    headlen = len(ndlist[0])
    return reduce(lambda acc, lst: type(lst) == lst and len(lst) == headlen and acc, ndlist, True)


def transpose(ndlist):
    if not all_same_length(ndlist):
        ndlist.pop()
    return np.array(ndlist).T.tolist()


def make_grid_layout(nx_graph, with_edge=True):
    """networkx graph를 받아서, GraphViz dot 포맷을 빌드한다."""
    graph = graphviz.Digraph()

    list_of_nodes = list(nx_graph.nodes)
    partitioned = partition(list_of_nodes, 5)  # 5 * n 사이즈로 만들어 봅시다!
    partitioned_T = transpose(partitioned)

    for node_name in list_of_nodes:
        if node_name in skip_funcs:
            graph.node(node_name, style="filled", fillcolor="purple")
        else:
            graph.node(node_name)

    for part in partitioned_T:
        bicycle_chain = make_bicycle_chain(part)
        for tup in bicycle_chain:
            graph.edge(*tup, style="invis")

    for part in partitioned:
        subgraph_command = make_subgraph_command("graph", part)
        exec(subgraph_command, globals(), locals())

    list_of_edges = list(nx_graph.edges)

    if with_edge:
        for edge in nx_graph.edges:
            edgekind = nx_graph.get_edge_data(*edge)["kind"]
            if edgekind == "df":
                graph.edge(edge[0], edge[1], color="red")
            elif edgekind == "call":
                graph.edge(edge[0], edge[1], color="black")
            elif edgekind == "sim":
                graph.edge(edge[0], edge[1], color="blue")
            else:
                raise ValueError(f"invalid edge data: {edgekind}")

    return graph


def main():
    graph0 = nx.read_gpickle("Decision-1.1.0_graph_0")
    make_BN.tame_rich(graph0)   # to simulate the making of BN

    # without edges
    dot_graph_without_edge = make_grid_layout(graph0, with_edge=False)
    dot_graph_without_edge.render(filename="graph0_without_edge",
                                  format="pdf",
                                  view=False,
                                  quiet=True,
                                  cleanup=True)

    # with colored edges
    dot_graph_with_edge = make_grid_layout(graph0, with_edge=True)
    dot_graph_with_edge.render(filename="graph0_with_edge",
                               format="pdf",
                               view=False,
                               quiet=True,
                               cleanup=True)

    print("done!")


if __name__ == "__main__":
    main()
