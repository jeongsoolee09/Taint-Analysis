import modin.pandas as pd
import networkx as nx
import os.path
import glob
import copy

from make_underlying_graph import df_reader, call_reader, extract_filename

# Paths and constants ======================================================
# ==========================================================================

upper_path = os.path.abspath("..")

SAGAN_SITE_PATH = os.path.join(upper_path, 'benchmarks',
                               'realworld', 'sagan', 'sagan-site')
SAGAN_RENDERER_PATH = os.path.join(upper_path, 'benchmarks',
                                   'realworld', 'sagan', 'sagan-renderer')

NODE_DATA = pd.read_csv("raw_data.csv", index_col=0, header=0)
EDGES_DATA = pd.read_csv("edges.csv", index_col=0, header=[0,1])


# Collecting subgraphs ====================================================
# =========================================================================

def collect_root_methods(path):
    # collecting root methods' classes
    global NODE_DATA
    root_files = []
    for current_dir, directories, files in os.walk(path):
        if "test" in current_dir:
            continue
        root_files += glob.glob(os.path.join(current_dir, "*.java"))
    root_classes = list(map(extract_filename, root_files))

    # collecting root methods
    mapfunc = lambda row: row['pkg'] in root_classes
    bool_column = NODE_DATA.apply(mapfunc, axis=1)
    NODE_DATA["is_root"] = bool_column
    root_methods = NODE_DATA[NODE_DATA.is_root != False]
    NODE_DATA = NODE_DATA.drop(columns=["is_root"])
    root_methods = root_methods.drop(columns=["is_root"])
    return root_methods


def collect_callees(G, root_methods):
    callees = []
    for root_node in root_methods:
        try:  # TODO: 디버깅
            callees += nx.dfs_preorder_nodes(graph_for_reference, source=root_node)
        except:
            continue
    callees = list(set(callees))
    return callees


def mask_graph(G, methods):
    masked_graph = copy.deepcopy(G)
    for node_name in list(masked_graph.nodes):
        if node_name not in methods:
            masked_graph.remove_node(node_name)
    return masked_graph


def main():
    graph_for_reference = nx.read_gpickle("graph_for_reference")

    sagan_site_root_methods = collect_root_methods(SAGAN_SITE_PATH)['id']
    sagan_renderer_root_methods = collect_root_methods(SAGAN_RENDERER_PATH)['id']
    
    sagan_site_methods = collect_callees(graph_for_reference, sagan_site_root_methods)
    sagan_renderer_methods = collect_callees(graph_for_reference, sagan_renderer_root_methods)
    
    sagan_site_graph = mask_graph(graph_for_reference, sagan_site_methods)
    sagan_renderer_graph = mask_graph(graph_for_reference, sagan_renderer_methods)

    nx.write_gpickle(sagan_site_graph, "sagan_site_graph")
    nx.write_gpickle(sagan_renderer_graph, "sagan_renderer_graph")
