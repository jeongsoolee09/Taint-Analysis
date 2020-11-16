import pandas as pd
import csv
import networkx as nx
import time
import glob
import random
import os.path
import json
import matplotlib.pyplot as plt

from create_node import process
from scrape_oracle_docs import scrape_class_names


def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]


PROJECT_ROOT_DIR = retrieve_path()


# readers ============================================
# ====================================================

# lazy loading csvs
edges = pd.read_csv("edges.csv", index_col=0, header=[0, 1])
edge_targets = edges.iloc[:, edges.columns.get_level_values(1) == "name"]

raw_data = open("nodes.csv", "r+")
data_reader = csv.reader(raw_data)

edges_data = open("edges.csv", "r+")
edges_reader = csv.reader(edges_data)


def is_java_builtin(method_id, built_in_classes):
    """주어진 method가 java.lang 혹은 java.utils에 속하는지를 판별하는 predicate:
       class 이름을 보고 판단."""
    # oracle doc urls
    method_class = process(method_id)[0]
    return method_class in built_in_classes


# eagerly loaded (line by line) txts
df_data = open("df.csv", "r+")
df_reader = csv.reader(df_data)

call_data = open("callg.csv", "r+")
call_reader = csv.reader(call_data)

df_edges = list(df_reader)
call_edges = list(call_reader)
# skip_funcs = skip_func_reader()


# Blacklisting and Whitelisting ======================
# ====================================================

def create_whitelist_blacklist_files():
    whitelist_files, blacklist_files = [], []
    for current_dir, directories, files in os.walk(PROJECT_ROOT_DIR):
        if 'tests' in current_dir or 'test' in current_dir:
            blacklist_files += glob.glob(os.path.join(current_dir, "*.java"))
        if 'tests' not in current_dir and 'test' not in current_dir:
            whitelist_files += glob.glob(os.path.join(current_dir, "*.java"))
    return whitelist_files, blacklist_files


def recursively_collect_callee(classes, graph_for_reference):
    nodes = list(graph_for_reference.nodes)
    callees = []
    for class_ in classes:
        class_methods = list(filter(lambda node: process(node)[0] == class_, nodes))
        for class_method in class_methods:
            callees += nx.dfs_preorder_nodes(graph_for_reference, source=class_method)
    return callees


def extract_filename(path):
    """path에서 (확장자를 제외한) filename만을 추출한다."""
    _, tail = os.path.split(path)
    return tail.split('.')[0]


def create_whitelist_blacklist_classes():
    whitelist_files, blacklist_files = create_whitelist_blacklist_files()
    whitelist = list(map(extract_filename, whitelist_files))
    blacklist = list(map(extract_filename, blacklist_files))
    return whitelist, blacklist


# Methods for Graphs ================================
# ===================================================


def add_node_to_graph(G):
    """creates a graph for identifying root nodes"""
    next(data_reader)  # Headers don't taste good
    for data in data_reader:
        G.add_node(data[6])  # set the method ID as a node name


def find_root(G):
    roots = []
    for node in G.nodes:
        if G.in_degree(node) == 0:
            roots.append(node)
    return roots


def add_edge_to_graph(G):
    """adds edges to `reference graph` G"""
    next(edges_reader)
    next(edges_reader)
    for row in edges_reader:
        firstNodeID = row[5]
        secondNodeID = row[10]
        if (firstNodeID, secondNodeID) in df_edges:
            G.add_edge(firstNodeID, secondNodeID, kind="df")
        elif (firstNodeID, secondNodeID) in call_edges:
            G.add_edge(firstNodeID, secondNodeID, kind="call")
        else:
            G.add_edge(firstNodeID, secondNodeID, kind="sim")


def apply_blacklist(G, blacklist_classes, blacklist_callees, whitelist_classes, whitelist_callees):
    for method_name in list(G.nodes):
        if process(method_name)[0] in blacklist_classes:
            G.remove_node(method_name)
    for blacklist_callee in blacklist_callees:
        if blacklist_callee not in whitelist_callees and\
           process(blacklist_callee)[0] not in whitelist_classes:
            try:
                G.remove_node(blacklist_callee)  # DFS traversal의 source node였나 봄
            except:
                pass


def filter_edges_from_graph(G, built_in_classes):
    """graph_for_reference의 각 노드들에 대해, edge fan_in이 8보다 많다면,
       skip_func_reader가 읽어낸 함수들 중 java.lang과 java.utils의 메소드만을 골라낸다."""
    for node_name in G.nodes:
        in_edges = list(G.in_edges(nbunch=node_name))
        can_be_removed_edges = []
        for parent, child in in_edges:
            parent_class = process(parent)[0]
            if parent_class in built_in_classes and\
               len(list(G.out_edges(nbunch=parent))) > 1:
                can_be_removed_edges.append((parent, child))
        if len(can_be_removed_edges) > 0:  # 없앨 수 있는 엣지가 있다면
            while len(in_edges) > 6:
                if len(can_be_removed_edges) == 0:
                    # print("failed to reduce edges below 7, # of in_edges:", len(in_edges), node_name)
                    break  # 6개 밑으로 떨어지지 않았더라도 없앨 엣지가 다 떨어지면 컷
                random_edge = random.choice(can_be_removed_edges)
                G.remove_edge(*random_edge)
                can_be_removed_edges.remove(random_edge)
                in_edges.remove(random_edge)


def find_edges_of(graph_for_reference, node_name):
    """주어진 node_name을 갖는 노드의 모든 incoming edge를 찾아낸다."""
    lookup_edges = graph_for_reference.edges
    out = []
    for (m1, m2) in lookup_edges:
        if m2 == node_name:
            out.append((m1, m2))
    return out


def find_edge_labels(graph_for_reference, node_name):
    """하나의 node를 받아 그 node가 속한 모든 엣지의 각 종류(df, call, sim)를 판별한다."""
    edges = find_edges_of(graph_for_reference, node_name)
    out = []
    for edge in edges:
        if edge in df_edges:
            out.append((edge[0], "df"))
        elif edge in call_edges:
            out.append((edge[0], "call"))
        else:
            out.append((edge[0], "sim"))
    return out


def init_graph(built_in_classes):
    """Initialize a (directed acyclic) graph for reference."""
    G = nx.DiGraph()
    add_node_to_graph(G)
    add_edge_to_graph(G)
    # filter_edges_from_graph(G, built_in_classes)
    flip_sim_edges(G)
    return G


def label_edges(G):
    """graph_for_reference G를 받아서, 각 엣지에다 엣지의 종류를 표현하는 레이블을 붙여 준다."""
    print("labelling edges (this may take some time)..")
    for edge in G.edges:
        attr_dict = dict()
        if edge in df_edges:
            attr_dict[edge] = {'kind': 'df'}
        elif edge in call_edges:
            attr_dict[edge] = {'kind': 'call'}
        else:
            attr_dict[edge] = {'kind': 'sim'}
    nx.set_edge_attributes(G, attr_dict)


def flip_sim_edges(G):
    """노드를 순회하면서 너무 많은 similarity edge를 맞은 노드가 있는지 확인하고, 그런 노드가 있다면 엣지 방향을 뒤집어 준다."""
    for node_name in list(G.nodes):
        in_edges = list(G.in_edges(nbunch=node_name, data=True))
        remaining_sim_edges = list(filter(lambda edge: edge[2]['kind'] == 'sim', in_edges))
        while len(in_edges) > 4:
            try:
                parent, child, kind = remaining_sim_edges.pop()
            except IndexError:
                break
            if 1 < len(G.out_edges(nbunch=parent)):
                G.remove_edge(parent, child)
            # G.add_edge(child, parent, kind=kind)


def main():
    start = time.time()

    java_lang_url = 'https://docs.oracle.com/javase/7/docs/api/java/lang/package-summary.html'
    java_utils_url = 'https://docs.oracle.com/javase/8/docs/api/java/util/package-summary.html'
    java_lang_classes = scrape_class_names(java_lang_url)
    java_utils_classes = scrape_class_names(java_utils_url)
    built_in_classes = java_lang_classes + java_utils_classes
    whitelist_classes, blacklist_classes = create_whitelist_blacklist_classes()

    graph_for_reference = init_graph(built_in_classes)

    whitelist_callees = recursively_collect_callee(whitelist_classes, graph_for_reference)
    blacklist_callees = recursively_collect_callee(blacklist_classes, graph_for_reference)
    apply_blacklist(graph_for_reference, blacklist_classes, blacklist_callees, whitelist_classes, whitelist_callees)

    nx.write_gpickle(graph_for_reference, "graph_for_reference")

    print("elapsed time:", time.time()-start)


if __name__ == "__main__":
    main()
