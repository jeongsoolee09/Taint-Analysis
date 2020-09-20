import modin.pandas as pd
import networkx as nx
import os.path
import glob
import copy
import csv
import random
import json

from make_underlying_graph import df_reader, call_reader, extract_filename
from community_detection import bisect
from find_jar import real_jar_paths, take_jar_dir


# Paths and constants ======================================================
# ==========================================================================

def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]


PROJECT_ROOT_PATH = retrieve_path()

JAR_PATHS = real_jar_paths(PROJECT_ROOT_PATH)

NODE_DATA = pd.read_csv("nodes.csv", index_col=0, header=0)

edges_data = open("callg.csv", "r+")
edges_reader = csv.reader(edges_data)

# Collecting subgraphs ====================================================
# =========================================================================

def draw_callgraph():
    next(edges_reader)
    callgraph = nx.DiGraph()
    for row in edges_reader:
        class1 = row[1]
        rtntype1 = row[2]
        name1 = row[3]
        intype1 = "()" if row[4] == "void" else "("+row[4]+")"
        class2 = row[5]
        rtntype2 = row[6]
        name2 = row[7]
        intype2 = "()" if row[8] == "void" else "("+row[8]+")"
        firstNodeID = rtntype1+" "+class1+"."+name1+intype1
        secondNodeID = rtntype2+" "+class2+"."+name2+intype2
        callgraph.add_edge(firstNodeID, secondNodeID, kind="call")
    return callgraph


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
    mapfunc = lambda row: row['class'] in root_classes
    bool_column = NODE_DATA.apply(mapfunc, axis=1)
    NODE_DATA["is_root"] = bool_column
    root_methods = NODE_DATA[NODE_DATA.is_root != False]
    NODE_DATA = NODE_DATA.drop(columns=["is_root"])
    root_methods = root_methods.drop(columns=["is_root"])
    return root_methods


def collect_callees(G, root_methods):
    callees = []
    for root_node in root_methods:
        try:
            callees += nx.dfs_preorder_nodes(G, source=root_node)
        except:
            pass
    callees = list(set(callees))
    return callees


def mask_graph(G, methods):
    masked_graph = copy.deepcopy(G)
    for node_name in list(masked_graph.nodes):
        if node_name not in methods:
            masked_graph.remove_node(node_name)
    return masked_graph


# TODO: 마구 지울 것이 아니라, sim edge 위주로 지우게 하기
def decycle(G):
    print('decycling (this may take some time)..')
    while True:
        try:
            cycle_path_edges = nx.find_cycle(G)
        except:
            print("decycling done")
            return
        random_edge = random.choice(cycle_path_edges)
        G.remove_edge(*random_edge)


def take_direct_subdirectory(jar_path):
    full_jar_path = take_jar_dir(jar_path)
    splitted = full_jar_path.split(os.sep)
    return splitted[len(splitted)-1]
        

def split_large_graph(G):
    def split_large_graph_inner(acc, worklist):
        if worklist == []:
            return acc
        target = worklist.pop()
        if len(target.nodes) <= 400:
            acc.append(target)
        else:
            small1, small2 = bisect(target)
            worklist.append(small1)
            worklist.append(small2)
        return split_large_graph_inner(acc, worklist)
    return split_large_graph_inner([], [G])


def main():
    graph_for_reference = nx.read_gpickle("graph_for_reference")
    callgraph = draw_callgraph()

    for jar_path in JAR_PATHS:
        graph_name = take_direct_subdirectory(jar_path)
        root_methods = collect_root_methods(jar_path)['id']
        all_methods = collect_callees(callgraph, root_methods)
        masked_graph = mask_graph(graph_for_reference, all_methods)
        small_graphs = split_large_graph(masked_graph)
        i = 0
        for small_graph in small_graphs:
            decycle(small_graph)
            nx.write_gpickle(small_graph, graph_name+"_graph_"+str(i))
            i += 1


if __name__ == "__main__":
    main()
