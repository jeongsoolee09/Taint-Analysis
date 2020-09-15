import networkx as nx
from networkx.algorithms import community


def bisect(large_graph):
    """bisect the given graph"""
    node_set_A, node_set_B = community.kernighan_lin_bisection(large_graph.to_undirected())
    return recover_graph(node_set_A, large_graph), recover_graph(node_set_B, large_graph)


def recover_graph(small_node_set, original_graph):
    """small_node_set에서부터 small_graph를 복원해 낸다."""
    edges = original_graph.edges
    # 각 엣지 안에 들어 있는 노드들이 small_node_set의 원소인지를 판단하는 것으로 충분하다.
    filterfunc = lambda edge: edge[0] in small_node_set and edge[1] in small_node_set
    small_graph_edges = list(filter(filterfunc, edges))
    G = nx.DiGraph()
    G.add_nodes_from(small_node_set)
    G.add_edges_from(small_graph_edges)
    return G
