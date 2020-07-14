import networkx as nx
from functools import reduce

# initializing the graph.
G = nx.DiGraph()
G.add_node(1, under_construction=False, defined=True)
G.add_node(2, under_construction=False, defined=True)
G.add_node(3, under_construction=False, defined=True)
G.add_node(4, under_construction=False, defined=False)
G.add_node(5, under_construction=False, defined=False)
G.add_node(6, under_construction=False, defined=True)
G.add_node(7, under_construction=False, defined=False)
G.add_node(8, under_construction=False, defined=False)
G.add_node(9, under_construction=False, defined=False)
G.add_edge(1,4)
G.add_edge(4,7)
G.add_edge(7,9)
G.add_edge(2,5)
G.add_edge(5,7)
G.add_edge(3,7)
G.add_edge(6,8)
G.add_edge(8,9)

H = nx.DiGraph()
H.add_node(1, under_construction=False, defined=True)
H.add_node(2, under_construction=False, defined=True)
H.add_node(3, under_construction=False, defined=False)
H.add_node(4, under_construction=False, defined=False)
H.add_edge(1,3)
H.add_edge(1,4)
H.add_edge(2,4)


I = nx.DiGraph()
H.add_node(1, under_construction=False, defined=True)
H.add_node(2, under_construction=False, defined=True)
H.add_node(3, under_construction=False, defined=False)
H.add_node(4, under_construction=False, defined=False)
H.add_edge(1,3)
H.add_edge(1,4)
H.add_edge(2,4)


def forall(unary_pred, collection):
    return reduce(lambda acc, elem: unary_pred(elem) and acc, collection, True)


def undefined_parents_of(graph, node):
    out = []
    for parent in graph.predecessors(node):  # parent는 int type
        if not graph.nodes[parent]['defined']:
            out.append(parent)
    return out


def toyprocedure(graph, node):
    """Recursively resolve the dependencies."""
    print(node)
    if graph.nodes[node]['defined']:  # 현 노드가 정의되어 있다
        if len(list(graph.successors(node))) > 0:  # successor가 있다
            for succ in graph.successors(node):
                if graph.nodes[succ]['under_construction']:
                    return
                else:
                    toyprocedure(graph, succ)
        else:  # successor가 없다
            return
    else:  # 현 노드가 정의되어 있지 않다
        if forall(lambda pred: graph.nodes[pred]['defined'], graph.predecessors(node)):
            graph.nodes[node]['defined'] = True
            if len(list(graph.successors(node))) > 0:  # successor가 있다
                for succ in graph.successors(node):
                    if graph.nodes[succ]['under_construction']:
                        return
                    else:
                        toyprocedure(graph, succ)
            else:  # successor가 없다
                return
        else:
            graph.nodes[node]['under_construction'] = True
            for parent in undefined_parents_of(graph, node):
                toyprocedure(graph, parent)
            graph.nodes[node]['under_construction'] = False
            graph.nodes[node]['defined'] = True
            if len(list(graph.successors(node))) > 0:  # successor가 있다
                for succ in graph.successors(node):
                    if graph.nodes[succ]['under_construction']:
                        return
                    else:
                        toyprocedure(graph, succ)
            else:  # successor가 없다
                return


def findRoot(G):
    roots = []
    for node in G.nodes:  # node는 int type
        if G.in_degree(node) == 0:
            roots.append(node)
    return roots


toyprocedure(G, 1)
print('-'*50)
toyprocedure(H, 1)
