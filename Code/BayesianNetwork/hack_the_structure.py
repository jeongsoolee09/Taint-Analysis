import graphviz
import networkx as nx
import make_BN
import os
import re
import numpy as np

from functools import reduce

graph_files = [f for f in os.listdir('.') if re.match(r'.*_graph_[0-9]+$', f)]


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


def make_grid_layout(nx_graph):
    """networkx graph를 받아서, GraphViz dot 포맷을 빌드한다."""
    graph = graphviz.Digraph()

    list_of_nodes = list(nx_graph.nodes)
    partitioned = partition(list_of_nodes, 5)  # 5 * n 사이즈로 만들어 봅시다!
    partitioned_T = transpose(partitioned)

    for part in partitioned_T:
        bicycle_chain = make_bicycle_chain(part)
        for tup in bicycle_chain:
            graph.edge(*tup, style="invis")

    for part in partitioned:
        subgraph_command = make_subgraph_command("graph", part)
        exec(subgraph_command, globals(), locals())

    list_of_edges = list(nx_graph.edges)

    return graph, graph.source


def main():
    graph0 = nx.read_gpickle("Decision-1.1.0_graph_0")
    make_BN.tame_rich(graph0)   # to simulate the making of BN
    dot_graph, sourcecode = make_grid_layout(graph0)
    with open("graph0.dot", "w+") as f:
        f.write(sourcecode)
    dot_graph.render(filename="graph0",
                     format="pdf",
                     view=False,
                     quiet=True,
                     cleanup=True)
    print("done!")


if __name__ == "__main__":
    main()
