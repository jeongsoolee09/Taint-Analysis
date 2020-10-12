import modin.pandas as pd
import networkx as nx
import os.path
import glob
import copy
import csv
import random
import json
import hashlib                  # for making time.time() digest

from make_underlying_graph import df_reader, call_reader, extract_filename
from community_detection import bisect_optimal, bisect
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
        # print(list(map(lambda graph: len(graph.nodes), worklist)))
        target = worklist.pop()
        if len(target.nodes) <= max_graph_size:
            acc.append(target)
        else:
            small1, small2 = bisect_optimal(target)
            if len(small1.nodes) == 0 or len(small2.nodes) == 0:
                return None
            worklist.append(small1)
            worklist.append(small2)
    # print("acc: ", list(map(lambda graph: len(graph.nodes),acc)))
    return acc


def collect_graph_by_mag_single(G):
    """split_large_graph의 수정 버전, 그래프를 잘라 나가면서 구간별로 해당되는 그래프를 collect"""
    worklist = [G]
    acc = []

    fifty_to_hundred = []
    hundred_to_hundredfifty = []
    hundredfifty_to_twohundred = []
    twohundred_to_twohundredfifty = []
    twohundredfifty_to_threehundred = []
    threehundred_to_threehundredfifty = []

    while worklist != []:
        print(list(map(lambda graph: len(graph.nodes), worklist)))
        target = worklist.pop()
        
        # match on target
        if 300 <= len(target.nodes) < 350:
            if target not in threehundred_to_threehundredfifty:
                threehundred_to_threehundredfifty.append(target)
        elif 250 <= len(target.nodes) < 300:
            if target not in twohundredfifty_to_threehundred:
                twohundredfifty_to_threehundred.append(target)
        elif 200 <= len(target.nodes) < 250:
            if target not in twohundred_to_twohundredfifty:
                twohundred_to_twohundredfifty.append(target)
        elif 150 <= len(target.nodes) < 200:
            if target not in hundredfifty_to_twohundred:
                hundredfifty_to_twohundred.append(target)
        elif 100 <= len(target.nodes) < 150:
            if target not in hundred_to_hundredfifty:
                hundred_to_hundredfifty.append(target)
        elif 50 <= len(target.nodes) < 100:
            if target not in fifty_to_hundred:
                fifty_to_hundred.append(target)

        if len(target.nodes) <= 49:
            acc.append(target)
        else:
            small1, small2 = bisect_optimal(target)

            # match on small1
            if 300 <= len(small1.nodes) < 350:
                if small1 not in threehundred_to_threehundredfifty:
                    threehundred_to_threehundredfifty.append(small1)
            elif 250 <= len(small1.nodes) < 300:
                if small1 not in twohundredfifty_to_threehundred:
                    twohundredfifty_to_threehundred.append(small1)
            elif 200 <= len(small1.nodes) < 250:
                if small1 not in twohundred_to_twohundredfifty:
                    twohundred_to_twohundredfifty.append(small1)
            elif 150 <= len(small1.nodes) < 200:
                if small1 not in hundredfifty_to_twohundred:
                    hundredfifty_to_twohundred.append(small1)
            elif 100 <= len(small1.nodes) < 150:
                if small1 not in hundred_to_hundredfifty:
                    hundred_to_hundredfifty.append(small1)
            elif 50 <= len(small1.nodes) < 100:
                if small1 not in fifty_to_hundred:
                    fifty_to_hundred.append(small1)

            # match on small2
            if 300 <= len(small2.nodes) < 350:
                if small2 not in threehundred_to_threehundredfifty:
                    threehundred_to_threehundredfifty.append(small2)
            elif 250 <= len(small2.nodes) < 300:
                if small2 not in twohundredfifty_to_threehundred:
                    twohundredfifty_to_threehundred.append(small2)
            elif 200 <= len(small2.nodes) < 250:
                if small2 not in twohundred_to_twohundredfifty:
                    twohundred_to_twohundredfifty.append(small2)
            elif 150 <= len(small2.nodes) < 200:
                if small2 not in hundredfifty_to_twohundred:
                    hundredfifty_to_twohundred.append(small2)
            elif 100 <= len(small2.nodes) < 150:
                if small2 not in hundred_to_hundredfifty:
                    hundred_to_hundredfifty.append(small2)
            elif 50 <= len(small2.nodes) < 100:
                if small2 not in fifty_to_hundred:
                    fifty_to_hundred.append(small2)

            if len(small1.nodes) == 0:
                acc.append(small2)
                continue
            elif len(small2.nodes) == 0:
                acc.append(small1)
                continue

            worklist.append(small1)
            worklist.append(small2)

    return (fifty_to_hundred,
            hundred_to_hundredfifty,
            hundredfifty_to_twohundred,
            twohundred_to_twohundredfifty,
            twohundredfifty_to_threehundred,
            threehundred_to_threehundredfifty)


def collect_graphs_by_mag(G):
    """위의 collect_graph_by_mag_single 함수를 여러 번 사용해 크기별 서브그래프들을 모음"""
    fifty_to_hundred = []
    hundred_to_hundredfifty = []
    hundredfifty_to_twohundred = []
    twohundred_to_twohundredfifty = []
    twohundredfifty_to_threehundred = []
    threehundred_to_threehundredfifty = []

    while len(threehundred_to_threehundredfifty) < 10:
        a, b, c, d, e = collect_graphs_by_mag_single(G)
        fifty_to_hundred += a
        hundred_to_hundredfifty += b
        hundredfifty_to_twohundred += c
        twohundred_to_twohundredfifty += d
        twohundredfifty_to_threehundred += e
        threehundred_to_threehundredfifty += f

    return (fifty_to_hundred,
            hundred_to_hundredfifty,
            hundredfifty_to_twohundred,
            twohundred_to_twohundredfifty,
            twohundredfifty_to_threehundred,
            threehundred_to_threehundredfifty)


def main():
    graph_for_reference = nx.read_gpickle("graph_for_reference")
    callgraph = draw_callgraph()

    for jar_path in JAR_PATHS:
        graph_name = take_direct_subdirectory(jar_path)
        root_methods = collect_root_methods(jar_path)['id']
        all_methods = collect_callees(callgraph, root_methods)
        masked_graph = mask_graph(graph_for_reference, all_methods)
        nx.write_gpickle(masked_graph, graph_name+"_graph")
        optimal_max_graph_size = find_optimal_graph_size(masked_graph)
        small_graphs = split_large_graph(masked_graph, optimal_max_graph_size)
        i = 0
        for small_graph in small_graphs:
            decycle(small_graph)
            nx.write_gpickle(small_graph, graph_name+"_graph_"+str(i))
            i += 1


if __name__ == "__main__":
    main()
