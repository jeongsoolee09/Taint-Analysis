import networkx as nx
from networkx.algorithms import community

def bisect(large_graph):
    """bisect the given graph"""
    node_set_A, node_set_B = community.kernighan_lin_bisection(large_graph.to_undirected())
    naively_recovered_A = naive_recover_graph(node_set_A, large_graph)
    naively_recovered_B = naive_recover_graph(node_set_B, large_graph)
    recovered_A, recovered_B = minimize_isolated(naively_recovered_A, naively_recovered_B, large_graph)
    return recovered_A, recovered_B


def naive_recover_graph(small_node_set, original_graph):
    """small_node_set에서부터 small_graph를 복원해 낸다."""
    edges = original_graph.edges
    # 각 엣지 안에 들어 있는 노드들이 small_node_set의 원소인지를 판단하는 것으로 충분하다.
    filterfunc = lambda edge: edge[0] in small_node_set and edge[1] in small_node_set
    small_graph_edges = list(filter(filterfunc, edges))
    G = nx.DiGraph()
    G.add_nodes_from(small_node_set)
    G.add_edges_from(small_graph_edges)
    return G


def number_of_isolated_nodes(G):
    acc = []
    for node_name in G.nodes:
        if len(G.in_edges(nbunch=node_name)) == 0 and len(G.out_edges(nbunch=node_name)) == 0:
            acc.append(node_name)
    return len(acc)


def minimize_isolated(graph1, graph2, original_graph):
    graph1_isolated = []
    for node_name in graph1.nodes:
        if len(graph1.in_edges(nbunch=node_name)) == 0 and\
           len(graph1.out_edges(nbunch=node_name)) == 0:
            graph1_isolated.append(node_name)

    graph2_isolated = []
    for node_name in graph2.nodes:
        if len(graph2.in_edges(nbunch=node_name)) == 0 and\
           len(graph2.out_edges(nbunch=node_name)) == 0:
            graph2_isolated.append(node_name)
        
    original_edges = original_graph.edges

    for isolated1 in graph1_isolated:
        for node1, node2 in original_edges:
            if isolated1 == node1:
                graph1.remove_node(isolated1)
                graph2.add_node(isolated1)
                graph2.add_edge(isolated1, node2)
            elif isolated1 == node2:
                graph1.remove_node(isolated1)
                graph2.add_node(isolated1)
                graph2.add_edge(node2, isolated1)
            else:
                pass

    for isolated2 in graph2_isolated:
        for node1, node2 in original_edges:
            if isolated2 == node1:
                graph2.remove_node(isolated2)
                graph1.add_node(isolated2)
                graph1.add_edge(isolated2, node2)
            elif isolated2 == node2:
                graph2.remove_node(isolated2)
                graph1.add_node(isolated2)
                graph1.add_edge(node2, isolated2)
            else:
                pass

    return graph1, graph2
