import networkx as nx
from networkx.algorithms import community


def bisect(G):
    G = G.to_undirected()
    partition_generator = community.kernighan_lin_bisection(G)
    partitions = list(communities_generator)
    return partitions
