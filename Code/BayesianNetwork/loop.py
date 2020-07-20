from pomegranate import *
import time
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
import csv
import networkx as nx
import itertools as it
import os
import random
from make_CPT import *

start = time.time()

edges = pd.read_csv("edges.csv", index_col=0, header=[0, 1])
edge_targets = edges.iloc[:, edges.columns.get_level_values(1) == "name"]

raw_data = open("raw_data.csv", "r+")
data_reader = csv.reader(raw_data)

edges_data = open("edges.csv", "r+")
edges_reader = csv.reader(edges_data)


def df_reader():
    with open("df.txt", "r+") as df:
        lines = df.readlines()
        lines = list(map(lambda line: line.rstrip(), lines))
        lines = list(map(lambda line: line.split(", "), lines))
        lines = list(map(lambda line: tuple(line), lines))
    return lines


def call_reader():
    with open("callg.txt", "r+") as callg:
        lines = callg.readlines()
        lines = list(map(lambda line: line.rstrip(), lines))
        lines = list(map(lambda line: line.split(", "), lines))
        lines = list(map(lambda line: tuple(line), lines))
    return lines


df_edges = df_reader()
call_edges = call_reader()


# ===================================================
# Methods for Graphs ================================


def add_node_to_graph(G):
    """creates a graph for identifying root nodes"""
    next(data_reader)  # Headers don't taste good
    for data in data_reader:
        G.add_node(data[6])


def add_data_to_node(G):
    """adds data to each node needed for dependency solving algorithm"""
    for node in G.nodes():
        G.nodes[node]["under_construction"] = False
        if G.in_degree(node) == 0:
            G.nodes[node]["defined"] = True
        else:
            G.nodes[node]["defined"] = False


def find_root(G):
    roots = []
    for node in G.nodes:
        if G.in_degree(node) == 0:
            roots.append(node)
    return roots


def add_edge_to_graph(G):
    """adds edges to reference graph G"""
    next(edges_reader)
    next(edges_reader)
    for row in edges_reader:
        pkg1 = row[2]
        rtntype1 = row[3]
        name1 = row[4]
        intype1 = "()" if row[5] == "void" else "("+row[5]+")"
        pkg2 = row[7]
        rtntype2 = row[8]
        name2 = row[9]
        intype2 = "()" if row[10] == "void" else "("+row[10]+")"
        firstNodeID = rtntype1+" "+pkg1+"."+name1+intype1
        secondNodeID = rtntype2+" "+pkg2+"."+name2+intype2
        G.add_edge(firstNodeID, secondNodeID)


def find_edges_of(node):
    global graph_for_reference
    lookup_edges = graph_for_reference.edges
    out = []
    for (m1, m2) in lookup_edges:
        if m2 == node:
            out.append((m1, m2))
    return out


def find_edge_labels(node):
    """하나의 node를 받아 그 node가 속한 모든 엣지의 각 종류(df, call, sim)를 판별한다."""
    edges = find_edges_of(node)
    out = []
    for edge in edges:
        if edge in df_edges:
            out.append((edge[0], "df"))
        elif edge in call_edges:
            out.append((edge[0], "call"))
        else:
            out.append((edge[0], "sim"))
    return out


def init_graph():
    """Initialize a (directed acyclic) graph for reference."""
    G = nx.DiGraph()
    add_node_to_graph(G)
    add_edge_to_graph(G)
    add_data_to_node(G)
    return G


# ====================================================
# Methods for BNs ====================================


def create_roots_for_BN(G, BN):
    """identifies roots nodes from G and adds them to BN"""
    out = []
    for root in find_root(G):
        new_node = State(DiscreteDistribution({1.0: 0.25, 2.0: 0.25, 3.0: 0.25, 4.0: 0.25}), name=root)
        BN.add_state(new_node)
        out.append(new_node)
    return out


def find_parent_nodes(states, names):
    """state들 중에서 이름이 names와 매칭되는 state를 names의 index대로 리턴한다."""
    out = []
    for name in names:
        for state in states:
            if state.name == name:
                out.append(state)
    return out


def create_internal_node_for_BN(node, BN, prev_states):
    """BN에 internal node를 만들어 추가한다."""
    labels = [1, 2, 3, 4]       # src, sin, san, non
    parents_and_edges = find_edge_labels(node)
    parents = list(map(lambda tup: tup[0], parents_and_edges)) 
    edges = list(map(lambda tup: tup[1], parents_and_edges))
    parent_nodes = find_parent_nodes(prev_states, parents)
    parent_dist = list(map(lambda node: node.distribution, parent_nodes))
    probs = create_CPT(edges).transpose().flatten()
    cond_prob_table_width = len(list(graph_for_reference.predecessors(node)))
    cond_prob_table_gen = it.repeat(labels, cond_prob_table_width+1)
    cond_prob_table = list(cond_prob_table_gen)
    cond_prob_table = it.product(*cond_prob_table)
    cond_prob_table = it.chain.from_iterable(cond_prob_table)
    cond_prob_table = np.fromiter(cond_prob_table, float).reshape(-1, cond_prob_table_width+1)
    cond_prob_table = np.c_[cond_prob_table, probs]
    cond_prob_table = cond_prob_table.tolist()
    cond_prob_table = ConditionalProbabilityTable(cond_prob_table, parent_dist)
    new_node = State(cond_prob_table, name=node)
    BN.add_state(new_node)
    return new_node


def forall(unary_pred, collection):
    return reduce(lambda acc, elem: unary_pred(elem) and acc, collection, True)


def undefined_parents_of(graph, node):
    out = []
    for parent in graph.predecessors(node):
        if not graph.nodes[parent]['defined']:
            out.append(parent)
    return out


# state objects in BN_for_inference.
BN_states = []


def create_internal_nodes_for_BN(BN, node, states):
    """Recursively resolve the dependencies."""
    global BN_states
    if graph_for_reference.nodes[node]['defined']:
        if len(list(graph_for_reference.successors(node))) > 0:
            for succ in graph_for_reference.successors(node):
                if graph_for_reference.nodes[succ]['under_construction']:
                    return
                else:
                    create_internal_nodes_for_BN(BN, succ, states)
        else:
            return
    else:
        if forall(lambda pred: graph_for_reference.nodes[pred]['defined'], graph_for_reference.predecessors(node)):
            new_state = create_internal_node_for_BN(node, BN, states)
            graph_for_reference.nodes[node]['defined'] = True
            BN_states.append(new_state)
            if len(list(graph_for_reference.successors(node))) > 0:
                for succ in graph_for_reference.successors(node):
                    if graph_for_reference.nodes[succ]['under_construction']:
                        return
                    else:
                        create_internal_nodes_for_BN(BN, succ, states+[new_state])
            else:
                return
        else:
            graph_for_reference.nodes[node]['under_construction'] = True
            for parent in undefined_parents_of(graph_for_reference, node):
                create_internal_nodes_for_BN(BN, parent, states)
            graph_for_reference.nodes[node]['under_construction'] = False
            new_state = create_internal_node_for_BN(node, BN, states)
            graph_for_reference.nodes[node]['defined'] = True
            BN_states.append(new_state)
            if len(list(graph_for_reference.successors(node))) > 0:
                for succ in graph_for_reference.successors(node):
                    if graph_for_reference.nodes[succ]['under_construction']:
                        return
                    else:
                        create_internal_nodes_for_BN(BN, succ, states+[new_state])
            else:
                return


def state_lookup(node_name):
    for state in BN_states:
        if state.name == node_name:
            return state


def add_edge_to_BN(BN):
    """adds edges to BN"""
    for edge in graph_for_reference.edges:
        node1, node2 = edge
        state1 = state_lookup(node1)
        state2 = state_lookup(node2)
        BN.add_edge(state1, state2)


def init_BN():
    global BN_states
    BN = BayesianNetwork("Interactive Inference of Taint Method Specifications")
    root_states = create_roots_for_BN(graph_for_reference, BN) 
    BN_states = BN_states + root_states
    sample_root = find_root(graph_for_reference)[0]
    create_internal_nodes_for_BN(BN, sample_root, root_states)
    add_edge_to_BN(BN)
    BN.bake()
    return BN

# ====================================================

graph_for_reference = init_graph()
BN_for_inference = init_BN()


def tuplestring_to_tuple(tuple_string):
    string_list = tuple_string.split(", ")
    if len(string_list) == 3:
        string_list = [string_list[0], string_list[1]+", "+string_list[2]]
    string_list[0] = string_list[0].lstrip('(')
    string_list[1] = string_list[1].rstrip(')')
    string_list[1] = string_list[1]+')'
    return (string_list[0], string_list[1])


def parse_chain(var_and_chain):
    var = var_and_chain[0]
    chain = var_and_chain[1]
    chain = chain.split(" -> ")
    chain = list(filter(lambda string: string != "", chain))
    chain = list(map(lambda item: item.lstrip(), chain))
    chain = list(map(lambda string: tuplestring_to_tuple(string), chain))
    return [var, chain]


def create_var_and_chain():
    """access path와 그 chain을 만든다. 이 때, ->로 연결되어 있던 chain은 모두 서브스트링으로 따로따로 분리된 상태이다."""
    current_path = os.path.abspath("..")
    chainfile = os.path.join(current_path, "benchmarks", "fabricated", "Chain.txt")
    with open(chainfile, "r+") as chain:
        lines = chain.readlines()
        var_to_chain = list(filter(lambda line: line != "\n", lines))
        var_to_chain = list(map(lambda line: line.rstrip(), var_to_chain))
        var_and_chain = list(map(lambda line: line.split(": "), var_to_chain))
        var_and_chain = list(map(lambda lst: parse_chain(lst), var_and_chain))
    return var_and_chain


def collect_src(chain_without_var):  # priority 4
    out = []
    chain_head = chain_without_var[0]
    if "Define" in chain_head[1]:  # sanity check
        activity = chain_head[1]
        callee_methname = activity.split("using")[1]
        callee_methname = callee_methname.lstrip(" ")
        out.append(callee_methname)
    return out


def collect_san(chain_without_var):  # priority 3
    out = []
    for (meth, activity) in chain_without_var:
        if "Redefine" in activity:
            out.append(meth)
    return out


def collect_sin(chain_without_var):  # priority 2
    out = []
    chain_end = chain_without_var[len(chain_without_var)-1]
    if "Dead" in chain_end[1]:
        out.append(chain_end[0])
    return out


def collect_non(chain_without_var, src_s, san_s, sin_s, setofallmethods):
    # priority 1
    src_s = set(src_s)
    san_s = set(san_s)
    sin_s = set(sin_s)
    setofallmethods = set(setofallmethods)
    non_suspects = list(setofallmethods - src_s - san_s - sin_s)
    return non_suspects


# should be called AFTER graph_for_reference is constructed
def create_tactics(chain_without_var):
    """consuming a chain in tuple list form, plans ahead how to question the oracle"""
    setofallmethods = graph_for_reference.nodes()
    src_suspects = collect_src(chain_without_var)  # priority 4
    san_suspects = collect_san(chain_without_var)  # priority 3
    sin_suspects = collect_sin(chain_without_var)  # priority 2
    non_suspects = collect_non(chain_without_var, src_suspects,
                               san_suspects, sin_suspects, setofallmethods)  # priority 1
    return {"src": src_suspects, "san": san_suspects,
            "sin": sin_suspects, "non": non_suspects}


var_and_chain = create_var_and_chain()

# 각 variable의 관점에서 본 src/sin/san/non
tactics_per_var = list(map(lambda x: (x[0], create_tactics(x[1])), var_and_chain))


def random_loop(current_asked, current_evidence):
    """the main interaction functionality, asking randomly"""
    i = random.randint(0, len(BN_for_inference.states)-1)
    state_names = list(map(lambda node: node.name, BN_for_inference.states))
    query = state_names[i]
    if set(current_asked) == set(state_names):
        print("nothing more to ask!")
        return
    while query in current_asked:
        i = random.randint(0, len(BN_for_inference.states)-1)
        query = BN_for_inference.states[i].name
    oracle_response = input("What label does <" + query + "> bear? [src/sin/san/non]: ")
    if oracle_response == 'src':
        current_evidence[query] = 1
        snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(state_names, snapshot)
        random_loop(current_asked+[query], current_evidence)
    elif oracle_response == 'sin':
        current_evidence[query] = 2
        snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(state_names, snapshot)
        random_loop(current_asked+[query], current_evidence)
    elif oracle_response == 'san':
        current_evidence[query] = 3
        snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(state_names, snapshot)
        random_loop(current_asked+[query], current_evidence)
    elif oracle_response == 'non':
        current_evidence[query] = 4
        snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(state_names, snapshot)
        random_loop(current_asked+[query], current_evidence)


def d_separation(node, givens):
    """givens에 있는 노드들에 대한, node와 조건부 독립인 노드들을 찾아낸다. Complexity: O(n)."""
    out = []
    for other_node in graph_for_reference.nodes:
        ancestral_graph = undefined



def tactical_loop(current_asked, current_evidence):
    """the main interaction functionality, asking tactically using d-separation"""
    i = random.randint(0, len(BN_for_inference.states)-1)
    state_names = list(map(lambda node: node.name, BN_for_inference.states))
    query = state_names[i]
    if set(current_asked) == set(state_names):
        print("nothing more to ask!")
        return
    while query in current_asked:
        i = random.randint(0, len(BN_for_inference.states)-1)
        query = BN_for_inference.states[i].name
    oracle_response = input("What label does <" + query + "> bear? [src/sin/san/non]: ")
    if oracle_response == 'src':
        current_evidence[query] = 1
        snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(state_names, snapshot)
        tactical_loop(current_asked+[query], current_evidence)
    elif oracle_response == 'sin':
        current_evidence[query] = 2
        snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(state_names, snapshot)
        tactical_loop(current_asked+[query], current_evidence)
    elif oracle_response == 'san':
        current_evidence[query] = 3
        snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(state_names, snapshot)
        tactical_loop(current_asked+[query], current_evidence)
    elif oracle_response == 'non':
        current_evidence[query] = 4
        snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(state_names, snapshot)
        tactical_loop(current_asked+[query], current_evidence)


def normalize_dist(oracle_response):
    """*int로 주어진* oracle_response에 따라 4-nomial distribution을 만든다."""
    if oracle_response == 1:
        return {1.0: 1, 2.0: 0, 3.0: 0, 4.0: 0}
    elif oracle_response == 2:
        return {1.0: 0, 2.0: 1, 3.0: 0, 4.0: 0}
    elif oracle_response == 3:
        return {1.0: 0, 2.0: 0, 3.0: 1, 4.0: 0}
    elif oracle_response == 4:
        return {1.0: 0, 2.0: 0, 3.0: 0, 4.0: 1}


def find_max_val(stats):
    max_key = max(stats, key=lambda key: stats[key])
    if max_key == 1.0:
        return "src"
    elif max_key == 2.0:
        return "sin"
    elif max_key == 3.0:
        return "san"
    elif max_key == 4.0:
        return "non"


colordict = {"src": "red", "sin": "orange", "san": "yellow", "non": "green"}


def create_colormap(names_and_labels):
    """BN을 기준으로 계산된 names_and_labels를 받아서 graph_for_reference를 기준으로 한 colormap을 만든다."""
    out = list(graph_for_reference.nodes)[:]
    for name, label in names_and_labels:
        index = out.index(name)
        out[index] = colordict[label]
    return out
        

def visualize_snapshot(node_name_list, snapshot):
    """한번 iteration 돌 때마다, 전체 BN의 snapshot을 가시화한다."""
    plt.clf()
    dists = []
    for dist in snapshot:
        if type(dist) == int:  # oracle에 의해 고정된 경우!
            dists.append(normalize_dist(dist))
        else:
            dists.append(dist.parameters[0])
    names_and_dists = list(zip(node_name_list, dists))
    names_and_labels = list(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists))
    colormap = create_colormap(names_and_labels)
    nx.draw(graph_for_reference, node_color=colormap,
            pos=nx.circular_layout(graph_for_reference),
            with_labels=True, node_size=100)
    plt.show()


def report_statistics():
    """meta-functionality for debugging"""
    print("# of nodes: ", len(list(BN_for_inference.states)))
    print("# of edges: ", len(list(BN_for_inference.edges)))
    print("elapsed time: ", time.time() - start)


def plot_graph():
    """단순하게 underlying graph만 출력한다."""
    plt.clf()
    nx.draw(graph_for_reference, font_size=8, with_labels=True,
            pos=nx.circular_layout(graph_for_reference))
    plt.show()


raw_data.close()
edges_data.close()


if __name__ == "__main__":
    random_loop(list(), dict())