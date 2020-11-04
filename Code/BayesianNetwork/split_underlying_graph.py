import modin.pandas as pd
import networkx as nx
import os.path
import glob
import copy
import csv
import random
import json
import hashlib
import time
import os

from make_underlying_graph import df_reader, call_reader, extract_filename
from community_detection import bisect_optimal, bisect, isolated_nodes, rich_nodes
from find_jar import real_jar_paths, take_jar_dir
from functools import reduce

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

MAX_GRAPH_SIZE = 170

edges_data = open("callg.csv", "r+")
edges_reader = csv.reader(edges_data)

# Collecting subgraphs ====================================================
# =========================================================================

def draw_callgraph():
    next(edges_reader)
    next(edges_reader)
    callgraph = nx.DiGraph()
    for row in edges_reader:
        firstNodeID = row[5]
        secondNodeID = row[10]
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


def is_vulnerable(G,node):
    return (G.in_edges(nbunch=node) == 0 or G.out_edges(nbunch=node) == 1) or\
           (G.in_edges(nbunch=node) == 1 or G.out_edges(nbunch=node) == 0)


def find_edge_to_erase(G, cycle_path_edges):
    nodes = dict(cycle_path_edges).keys()
    erasable_nodes = []
    for node in nodes:
        # check if node is about to be poor
        if not is_vulnerable(G, node):
            erasable_nodes.append(node)

    # find an edge we can erase
    erasable_edges = []
    for node1, node2 in cycle_path_edges:
        if node1 in erasable_nodes and node2 in erasable_nodes:
            erasable_edges.append((node1, node2))
    return random.choice(erasable_edges)


def decycle(G):
    print('decycling (this may take some time)..')
    print("# of nodes:", len(G.nodes))
    print('# of rich nodes before decycling:', len(isolated_nodes(G)))
    print('# of isolated nodes before decycling:', len(rich_nodes(G)))
    while True:
        try:
            cycle_path_edges = nx.find_cycle(G)
        except:
            print("decycling done")
            print('# of rich nodes after decycling:', len(rich_nodes(G)))
            print('# of isolated nodes after decycling:', len(isolated_nodes(G)))
            return
        random_edge = find_edge_to_erase(G, cycle_path_edges)
        G.remove_edge(*random_edge)


def take_direct_subdirectory(jar_path):
    full_jar_path = take_jar_dir(jar_path)
    splitted = full_jar_path.split(os.sep)
    return splitted[len(splitted)-1]


def exists(unary_pred, coll):
    return reduce(lambda acc, elem: acc or unary_pred(elem), coll, False)


def find_optimal_graph_size(G):
    max_graph_size = 200
    while True:
        # print(max_graph_size)
        # for _ in range(5):
        small_graphs = split_large_graph(G, max_graph_size)
        if small_graphs == None:  # we have reached the lower bound
            print("optimal graph size is", max_graph_size+1)
            return max_graph_size+1
        graph_num_of_nodes = list(map(lambda graph: len(graph.nodes), small_graphs))
        if exists(lambda length: length < 80, graph_num_of_nodes):  # we are about to reach the lower bound
            print("optimal graph size is", max_graph_size+1)
            return max_graph_size+1
        max_graph_size -= 1


def split_large_graph(G, max_graph_size):
    worklist = [G]
    acc = []
    while worklist != []:
        print(list(map(lambda graph: len(graph.nodes), worklist)))
        target = worklist.pop()
        if len(target.nodes) <= max_graph_size:
            acc.append(target)
        else:
            small1, small2 = bisect(target)
            print(len(isolated_nodes(small1)))
            print(len(isolated_nodes(small2)))
            # if len(small1.nodes) == 0 or len(small2.nodes) == 0:
            #     return None
            if len(small1.nodes) != 0:
                worklist.append(small1)
            if len(small2.nodes) != 0:
                worklist.append(small2)
    # print("acc: ", list(map(lambda graph: len(graph.nodes),acc)))
    return acc


def main():
    graph_for_reference = nx.read_gpickle("graph_for_reference")
    callgraph = draw_callgraph()

    if JAR_PATHS != []:
        for jar_path in JAR_PATHS:
            graph_name = take_direct_subdirectory(jar_path)
            root_methods = collect_root_methods(jar_path)['id']
            all_methods = collect_callees(callgraph, root_methods)
            masked_graph = mask_graph(graph_for_reference, all_methods)
            nx.write_gpickle(masked_graph, graph_name+"_graph")
            # optimal_max_graph_size = find_optimal_graph_size(masked_graph)
            small_graphs = split_large_graph(masked_graph, 180)
            i = 0
            for small_graph in small_graphs:
                decycle(small_graph)
                nx.write_gpickle(small_graph, graph_name+"_graph_"+str(i))
                i += 1
        nx.write_gpickle(callgraph, "callgraph")

    else:                       # There are no .jar files in PROJECT_ROOT
        small_graphs = split_large_graph(graph_for_reference, 180)
        i = 0
        for small_graph in small_graphs:
            decycle(small_graph)
            nx.write_gpickle(small_graph, graph_name+"_graph_"+str(i))
            i += 1
        nx.write_gpickle(callgraph, "callgraph")


if __name__ == "__main__":
    main()
