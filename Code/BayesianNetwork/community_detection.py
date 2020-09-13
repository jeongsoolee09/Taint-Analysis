import networkx as nx
from networkx.algorithms import community

G = nx.read_gpickle("sagan_site_graph")
G = G.to_undirected()
communities_generator = community.kernighan_lin_bisection(G)
communities = list(communities_generator)
lens = list(map(lambda x: len(x), communities))
