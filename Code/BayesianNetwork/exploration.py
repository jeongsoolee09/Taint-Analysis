import networkx as nx
import networkx.algorithms as nxalg

from itertools import product, combinations
from community_detection import rich_nodes


MOTHER = nx.read_gpickle("graph_for_reference")

with open("../benchmarks/realworld/FFI/Decision-1.1.0/skip_func.txt", "r+") as skip_func:
    SKIP_FUNCS = skip_func.readlines()
    SKIP_FUNCS = list(map(lambda string: string.rstrip(), SKIP_FUNCS))


def create_path_string(graph_for_reference, from_node, to_node):
    """BN 상에서 from_node로부터 to_node까지, update가 일어난 path들을 모두 pretty print."""

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
    paths = list(nxalg.simple_paths.all_simple_paths(BN_undirected, from_node, to_node))

    acc = []

    i = 1
    for path in paths:
        string = "path"+str(i)+":", inner(path, graph_for_reference)
        acc.append(string)
        i += 1

    return acc


def main():
    APIs = list(filter(lambda node: node in SKIP_FUNCS, MOTHER.nodes))
    nodes_combs = list(combinations(APIs, 2))
    acc = []
    for node1, node2 in nodes_combs:
        acc += create_path_string(MOTHER, node1, node2)
    with open("mother_paths.txt", "w+") as f:
        for string in acc:
            f.write(string+"\n")


if __name__ == "__main__":
    main()
