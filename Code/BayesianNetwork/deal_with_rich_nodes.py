import networkx as nx
import copy


def is_vulnerable(G, node):
    """G 안에 속한 node가 자신과 연결된 엣지를 지우면 안 되는 노드인지를 판별"""
    return (G.in_edges(nbunch=node) == 0 or G.out_edges(nbunch=node) == 1) or\
           (G.in_edges(nbunch=node) == 1 or G.out_edges(nbunch=node) == 0)


# Heuristic No.1: rich_node의 incoming_edge 개수에 관계 없이 사용 가능
def delete_deletable_edges(G, rich_node):
    """날려도 되는 엣지들을 날리고, G를 리턴한다. 만약 모든 엣지들이 날릴 수 없는 엣지라면, None을 리턴한다."""
    in_edges = G.in_edges(nbunch=rich_node)
    out_edges = G.out_edges(nbunch=rich_node)
    all_edges = list(in_edges) + list(out_edges)

    deletable_edges = []
    for node1, node2 in all_edges:
        if node1 == rich_node:
            if not is_vulnerable(G, node2):
                deletable_edges.append((node1, node2))
        if node2 == rich_node:
            if not is_vulnerable(G, node1):
                deletable_edges.append((node1, node2))

    if deletable_edges != []:   # 날릴 수 있는 엣지 날리고 G 리턴
        for deletable_edge in deletable_edges:
            G.remove_edge(*deletable_edge)
        return G
    else:                       # G를 그냥 리턴
        return G


def make_all_possible_cases(edge_number):
    """input으로 2를 주면 ['00', '01', '10', '11'] 을 만들어 냄"""
    format_string = "{:0" + str(edge_number) + "b}"
    return list(map(lambda x: format_string.format(x), range(2**edge_number)))


# 엣지 뒤집는 방법: .remove_edge((u, v)) 한 다음 .add_edge(*(u, v)) 해 주면 됨.
def flip_selected_edges(G, edges_to_flip):
    for u, v in edges_to_flip:
        G.remove_edge(u, v)
        G.add_edge(v, u)


# Heuristic No.2: rich_node의 incoming_edge가 약 10 이하일 경우에만 사용 가능
def flip_edges_and_check(G, rich_node):
    """뒤집고/안 뒤집고의 모든 가능성인 2^k 가능성들을 모두 탐색하며, cycle이 없는 경우가 발견될 경우 곧바로 G를 리턴한다."""
    assert rich_node in list(G.nodes)

    in_edges = G.in_edges(nbunch=rich_node)
    out_edges = G.out_edges(nbunch=rich_node)
    all_edges = list(in_edges) + list(out_edges)

    number_of_edges = len(all_edges)

    # 0과 1로 표현된 모든 뒤집고/안 뒤집는 경우들
    all_possible_cases = make_all_possible_cases(number_of_edges)
    print(all_possible_cases)
    print("0"*number_of_edges)
    all_possible_cases.remove("0"*number_of_edges)

    for binary_possible_case in all_possible_cases:
        # 모든 엣지들과 0/1을 결부짓기
        all_possible_cases = list(zip(all_edges, binary_possible_case))

        # 1과 결부된 엣지들만들을 남기기
        edges_to_flip = list(filter(lambda tup: tup[1] == 1, all_possible_cases))
        edges_to_flip = list(map(lambda tup: tup[0], edges_to_flip))

        prev_G = G

        flip_selected_edges(G, edges_to_flip)

        assert prev_G != G

        try:
            nx.find_cycle(G)  # cycle이 없다면 곧바로 리턴
        except:
            return G


def main(G, rich_node):
    """No.2를 시도해 보고, 안 되면 No.1로 fallback한다. 그래도 안 되면 안 된다고 print하고, G를 단순히 리턴한다."""
    G_copy = copy.deepcopy(G)
    # heur1_G = delete_deletable_edges(G, rich_node)

    # if G_copy != heur1_G:
    #     return heur1_G
    # else:
    #     heur2_G = flip_edges_and_check(G_copy, rich_node)
    #     if heur2_G == heur1_G:
    #         print('None of the heuristics worked :(')
    #     return heur2_G
    heur2_G = flip_edges_and_check(G_copy, rich_node)
    if heur2_G == G_copy:
        print('None of the heuristics worked :(')
    return heur2_G

