import networkx as nx
from networkx.algorithms import community


def compute_error(original_graph, graph_A, graph_B):
    original_number_of_nodes = len(original_graph.nodes)
    error_A = abs(len(graph_A.nodes) - original_number_of_nodes//2)
    error_B = abs(len(graph_B.nodes) - original_number_of_nodes//2)
    return error_A+error_B


def bisect_optimal(large_graph, mother_graph):
    acc = []
    for _ in range(100):
        A, B = bisect(large_graph)
        error = compute_error(large_graph, A, B)
        acc.append((A, B, error))
    best_pair = min(acc, key=lambda tup: tup[2])
    best_A = best_pair[0]
    best_B = best_pair[1]
    return best_A, best_B


def bisect_naive(large_graph, mother_graph):
    """bisect the given graph"""
    node_set_A, node_set_B = community.kernighan_lin_bisection(large_graph.to_undirected())
    naively_recovered_A = naive_recover_graph(node_set_A, large_graph, mother_graph)
    naively_recovered_B = naive_recover_graph(node_set_B, large_graph, mother_graph)

    return naively_recovered_A, naively_recovered_B


def bisect(large_graph, mother_graph):
    """bisect the given graph"""
    node_set_A, node_set_B = community.kernighan_lin_bisection(large_graph.to_undirected())
    naively_recovered_A = naive_recover_graph(node_set_A, large_graph, mother_graph)
    naively_recovered_B = naive_recover_graph(node_set_B, large_graph, mother_graph)

    recovered_A, recovered_B = minimize_isolated(naively_recovered_A, naively_recovered_B, large_graph)
    return recovered_A, recovered_B


def naive_recover_graph(small_node_set, original_graph, mother_graph):
    """small_node_set에서부터 small_graph를 복원해 낸다."""
    # 각 엣지 안에 들어 있는 노드들이 small_node_set의 원소인지를 판단하는 것으로 충분하다.
    filterfunc = lambda edge: edge[0] in small_node_set and edge[1] in small_node_set
    small_graph_edges = list(filter(filterfunc, mother_graph.edges))
    G = nx.DiGraph()
    G.add_nodes_from(small_node_set)
    for edge in small_graph_edges:
        edge_data = mother_graph.get_edge_data(*edge)["kind"]
        G.add_edge(*edge, kind=edge_data)

    return G


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


def minimize_isolated(graph1, graph2, original_graph):
    # graph1_isolated = []
    # for node in isolated_nodes(graph1):
    #     graph1_isolated.append(node)

    graph1_isolated = [node for node in isolated_nodes(graph1)]

    # graph2_isolated = []
    # for node in isolated_nodes(graph2):
    #     graph2_isolated.append(node)

    graph2_isolated = [node for node in isolated_nodes(graph2)]

    original_edges = original_graph.edges

    for isolated1 in graph1_isolated:
        for node1, node2 in original_edges:
            if isolated1 == node1:
                try:
                    graph1.remove_node(node1)
                    graph2.add_node(node1)
                    edge_label = original_edges.get_edge_data(node1, node2)["kind"]
                    graph2.add_edge(node1, node2, kind=edge_label)
                except:
                    pass        # 이미 지웠네
            elif isolated1 == node2:
                try:
                    graph1.remove_node(isolated1)
                    graph2.add_node(isolated1)
                    edge_label = original_edges.get_edge_data(node2, isolated1)["kind"]
                    graph2.add_edge(node2, isolated1, kind=edge_label)
                except:
                    pass
            else:
                pass

    for isolated2 in graph2_isolated:
        for node1, node2 in original_edges:
            if isolated2 == node1:
                try:
                    graph2.remove_node(isolated2)
                    graph1.add_node(isolated2)
                    edge_label = original_edges.get_edge_data(isolated2, node2)["kind"]
                    graph1.add_edge(isolated2, node2, kind=edge_label)
                except:
                    pass
            elif isolated2 == node2:
                try:
                    graph2.remove_node(isolated2)
                    graph1.add_node(isolated2)
                    edge_label = original_edges.get_edge_data(node2, isolated2)["kind"]
                    graph1.add_edge(node2, isolated2, kind=edge_label)
                except:
                    pass
            else:
                pass

    return graph1, graph2
