import networkx as nx


def is_vulnerable(G,node):
    """G 안에 속한 node가 자신과 연결된 엣지를 지우면 안 되는 노드인지를 판별"""
    return (G.in_edges(nbunch=node) == 0 or G.out_edges(nbunch=node) == 1) or\
           (G.in_edges(nbunch=node) == 1 or G.out_edges(nbunch=node) == 0)


# Heuristic No.1: rich_node의 incoming_edge 개수에 관계 없이 사용 가능
def delete_deletable_edge(G, rich_node):
    """날려도 되는 엣지들을 날리고, G를 리턴한다. 만약 모든 엣지들이 날릴 수 없는 엣지라면, None을 리턴한다."""
    in_edges = G.in_edges(nbunch=rich_node)
    out_edges = G.out_edges(nbunch=rich_node)
    all_edges = in_edges + out_edges

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
            G.remove_edge(deletable_edge)
        return G
    else:                       # G를 그냥 리턴
        return G
        

# Heuristic No.2: rich_node의 incoming_edge가 약 10 이하일 경우에만 사용 가능
def flip_edges_and_check(rich_node):
    """뒤집고/안 뒤집고의 모든 가능성인 2^k 가능성들을 모두 탐색하며, cycle이 없는 경우가 발견될 경우 곧바로 G를 리턴한다."""
    pass


def main(G,node):
    """No.2를 시도해 보고, 안 되면 No.1로 fallback한다. 그래도 안 되면 안 된다고 print하고, G를 단순히 리턴한다."""
    # TODO gotta add some interesting fallback logics here:
    # delete_deletable_edge의 결과 그래프와 이전의 그래프가 동일하다면 flip_edges_and_check을 시도,
    # 아니라면 곧바로 G를 리턴
    pass
