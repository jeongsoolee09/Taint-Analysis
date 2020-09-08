import networkx as nx
import os.path

from make_underlying_graph import df_reader, call_reader

# Paths and constants ======================================================
# ==========================================================================

sagan_site_path = os.path.join(upper_path, 'benchmarks',
                               'realworld', 'sagan', 'sagan-site')
sagan_client_path = os.path.join(upper_path, 'benchmarks',
                                 'realworld', 'sagan', 'sagan-client')
sagan_renderer_path = os.path.join(upper_path, 'benchmarks',
                                   'realworld', 'sagan', 'sagan-renderer')

raw_data = open("raw_data.csv", "r+")
data_reader = csv.reader(raw_data)

edges_data = open("edges.csv", "r+")
edges_reader = csv.reader(edges_data)

# Collecting subgraphs ====================================================
# =========================================================================


def collect_sagan_site_roots():
    


def collect_sagan_client_roots():
    pass


def collect_sagan_renderer_roots():
    pass


def collect_sagan_site_callees(sagan_site_roots):
    pass


def collect_sagan_client_callees(sagan_client_root):
    pass


def collect_sagan_renderer_callees(sagan_renderer_roots):
    pass


def main():
    graph_for_reference = nx.read_gpickle("graph_for_reference")
    sagan_site_roots = 
