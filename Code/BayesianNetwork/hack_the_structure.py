import graphviz
import networkx as nx

from functools import reduce

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


def make_subgraph_command(digraph_var_name, partition):
    """flexing my metaprogramming skills"""
    command_for_elems = map(lambda s: f"    s.node(\"{s}\")\n", partition)
    all_commands = reduce(lambda a, e: a+e, command_for_elems)
    return f"""with {digraph_var_name}.subgraph() as s:
    s.attr(rank="same")
"""+all_commands


def make_grid_layout(nx_graph):
    """networkx graph를 받아서, GraphViz dot 포맷을 빌드한다."""
    list_of_nodes = list(nx_graph.nodes)
    partitioned = partition(list_of_nodes, 5)  # 5 * n 사이즈로 만들어 봅시다!

    d = graphviz.Digraph(filename="graph_0.dot")

    for part in partitioned:
        subgraph_command = make_subgraph_command("d", part)
        exec(subgraph_command, globals(), locals())


def main():
    graph0 = nx.read_gpickle("Decision-1.1.0_graph_0")
    make_grid_layout(graph0)


if __name__ == "__main__":
    main()
