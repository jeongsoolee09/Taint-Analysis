import networkx as nx
import copy
from community_detection import isolated_nodes, rich_nodes


def is_vulnerable(G, node):
    """G 안에 속한 node가 자신과 연결된 엣지를 지우면 안 되는 노드인지를 판별"""
    return (G.in_edges(nbunch=node) == 0 or G.out_edges(nbunch=node) == 1) or\
           (G.in_edges(nbunch=node) == 1 or G.out_edges(nbunch=node) == 0)


def can_stick_node_to(G, from_node, to_node):
    """node1을 node2에 붙일 수 있는가?"""
    if scoring_function(from_node, to_node) > 20 and\
       G.in_edges(nbunch=to_node) < 6:
        return True
    else:
        return False


def find_stickable_node(G, from_node, to_candidates, rich_node):
    """to_candidates 중에서 from_node가 엣지를 쏠 수 있는 노드를 찾아보고, 찾는 즉시 리턴한다.
       특히, rich_node를 제외한 다른 노드들에 붙일 수 있는가를 우선적으로 알아보고,
       하나도 없다면 그제서야 rich_node에 붙일 수 있는지를 알아본다.
       만약 rich_node에도 붙일 수 없다면 None을 리턴한다."""

    # 우선 rich_node가 아닌 노드들에 붙일 수 있는지를 알아보고, 찾으면 곧바로 리턴한다.
    for to_candidate in set(to_candidates)-{rich_node}:
        if can_stick_node_to(G, from_node, to_candidate):
            return to_candidiate
    # 만약 못 찾았다면 rich_node에 붙일 수 있는지를 알아본다.
    if can_stick_node_to(G, from_node, rich_node):
        return rich_node
    else:                       # 그래도 안 되면 하는 수 없이 None을 리턴한다.
        return None


def decompose_rich_node(G, rich_node):
    """rich_node의 neighbor들을 재배치함으로써 rich_node의 incoming edge 개수를 줄인다."""
    # 엣지를 쏘고 있는 노드들을 모두 rich node로부터 떼낸다.
    in_edges = list(G.in_edges(nbunch=rich_node))
    edge_shooters = []
    for other_node, _ in in_edges:
        edge_shooters.append(other_node)
    for in_edge in in_edges:
        G.remove_edge(*in_edge)

    G_copy = copy.deepcopy(G)
    G_copy.to_undirected()

    candidates = nx.node_connected_component(G_copy, rich_node)
    # 이제 엣지를 쏘고 있는 노드들은 모두 rich_node로부터 disconnect되었다.

    stash = []

    # edge_shooter들을 하나씩 pop해 나가면서,
    # 1. 만약 can 붙일 수 있는 노드에 노드를 붙이자.
    while edge_shooters != []:
        popped_node = edge_shooters.pop()
        stickable_node = find_stickable_node(G, popped_node)
        if stickable_node is not None:
            G.add_edge(popped_node, stickable_node)
        else:
            stash.append(popped_node)

    relocate_stashed_nodes(G, stash)


def main():
    # rich node를 identify한다.
    rich_nodes = rich_nodes(G)

    for rich_node in rich_nodes:
        decompose_rich_node(G, rich_node)
