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
from toolz import valmap
from make_CPT import *

start = time.time()

edges = pd.read_csv("edges.csv", index_col=0, header=[0, 1])
edge_targets = edges.iloc[:, edges.columns.get_level_values(1) == "name"]

raw_data = open("raw_data.csv", "r+")
data_reader = csv.reader(raw_data)

edges_data = open("edges.csv", "r+")
edges_reader = csv.reader(edges_data)


class ThisIsImpossible(exception):
    pass


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


def find_nodes_matching_names(states, names):
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
    parent_dist = list(map(lambda state: state.distribution, prev_states))
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


def find_BN_state(node_name, currently_defined_states):
    """node_name이 주어졌을 때, 지금까지 정의된 BN의 state들 중에서 이름이 node_name이랑 같은 노드를 내놓는다."""
    for state in currently_defined_states:
        if state.name == node_name:
            return state


def create_internal_nodes_for_BN(BN, currently_defined_states):
    """initialize the internal nodes using topological sort on graph_for_reference"""
    for node_name in list(nx.topological_sort(graph_for_reference)):
        if node_name in find_root(graph_for_reference):
            continue
        else:
            predecessor_names = list(graph_for_reference.predecessors(node_name))
            predecessor_nodes = list(map(lambda pred_name: find_BN_state(pred_name, currently_defined_states), predecessor_names))
            # print(list(map(lambda node: node.name, predecessor_nodes)))
            new_state = create_internal_node_for_BN(node_name, BN, predecessor_nodes)
            currently_defined_states.append(new_state)
    return currently_defined_states


def state_lookup(node_name, currently_defined_states):
    for state in currently_defined_states:
        if state.name == node_name:
            return state


def add_edge_to_BN(BN, currently_defined_states):
    """adds edges to BN"""
    for edge in graph_for_reference.edges:
        node1, node2 = edge
        state1 = state_lookup(node1, currently_defined_states)
        state2 = state_lookup(node2, currently_defined_states)
        BN.add_edge(state1, state2)


def init_BN():
    BN = BayesianNetwork("Interactive Inference of Taint Method Specifications")
    root_states = create_roots_for_BN(graph_for_reference, BN) 
    states = create_internal_nodes_for_BN(BN, root_states)
    add_edge_to_BN(BN, states)
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


def random_loop(current_asked, current_evidence, prev_snapshot, precision_list, stability_list):
    """the main interaction functionality, asking randomly"""
    i = random.randint(0, len(BN_for_inference.states)-1)
    state_names = list(map(lambda node: node.name, BN_for_inference.states))
    query = state_names[i]
    if set(current_asked) == set(state_names):
        print("nothing more to ask!")
        return prev_snapshot, precision_list, stability_list
    while query in current_asked:
        i = random.randint(0, len(BN_for_inference.states)-1)
        query = BN_for_inference.states[i].name
    oracle_response = input("What label does <" + query + "> bear? [src/sin/san/non]: ")
    if oracle_response == 'src':
        current_evidence[query] = 1
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(new_snapshot)
        current_precision_list = calculate_precision(new_snapshot)
        current_stability_list = calculate_stability(prev_snapshot, new_snapshot)
        return random_loop(current_asked+[query], current_evidence, new_snapshot,  precision_list+[current_precision_list], stability_list+[current_stability_list])
    elif oracle_response == 'sin':
        current_evidence[query] = 2
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(new_snapshot)
        current_precision_list = calculate_precision(new_snapshot)
        current_stability_list = calculate_stability(prev_snapshot, new_snapshot)
        return random_loop(current_asked+[query], current_evidence, new_snapshot,  precision_list+[current_precision_list], stability_list+[current_stability_list])
    elif oracle_response == 'san':
        current_evidence[query] = 3
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(new_snapshot)
        current_precision_list = calculate_precision(new_snapshot)
        current_stability_list = calculate_stability(prev_snapshot, new_snapshot)
        return random_loop(current_asked+[query], current_evidence, new_snapshot,  precision_list+[current_precision_list], stability_list+[current_stability_list])
    elif oracle_response == 'non':
        current_evidence[query] = 4
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(new_snapshot)
        current_precision_list = calculate_precision(new_snapshot)
        current_stability_list = calculate_stability(prev_snapshot, new_snapshot)
        return random_loop(current_asked+[query], current_evidence, new_snapshot,  precision_list+[current_precision_list], stability_list+[current_stability_list])


def d_connected(node, current_asked):
    """현재까지 물어본 노드들이 주어졌을 때, node와 조건부 독립인 노드들의 set을 찾아낸다. Complexity: O(n)."""
    out = set()
    for other_node in graph_for_reference.nodes:
        if nx.d_separated(graph_for_reference, {node}, {other_node}, set(current_asked)):
            out.add(other_node)
    return set(graph_for_reference.nodes) - out


def remove_nth_item(lst, index):
    """remove the nth element from list without any side-effect."""
    return lst[:index] + lst[index+1:]


def remove_sublist(lst, sublst):
    """remove the sublst from lst without any side-effect."""
    out = []
    for elem in lst:
        if elem not in sublst:
            out.append(i)
    return out


  # tactical_loop의 각 branch 맨 마지막마다 존재하는 return tactical_loop(...) 대용으로 쓸 control structure
def what_to_do_next(current_asked, updated_nodes, current_evidence, new_snapshot, precision_list, stability_list, current_precision_list, current_stability_list):
    """여러 변수를 종합적으로 고려해 봤을 때, 다음에 무엇을 해야 하는지를 알려준다."""
    # some variables to make our code resemble the English language
    there_are_nodes_left = find_max_d_con(current_asked, updated_nodes)
    there_are_no_nodes_left = not find_max_d_con(current_asked, updated_nodes)
    its_time_to_terminate = time_to_terminate(BN_for_inference, current_evidence)
    not_yet_time_to_terminate = not time_to_terminate(BN_for_inference, current_evidence)
    if there_are_no_nodes_left and not_yet_time_to_terminate:
        # backtracking mechanism: 가장 마지막에 물어봤던 노드의 영향을 없애고, find_max_d_con의 전체 스페이스에서 그 노드를 날린다. 다만 find_max_
        last_asked = current_asked[len(x)-1]  # popping without side-effect!
        previously_affected_nodes = d_connected(node, remove_nth_item(current_asked, len(x)-1))
        rollback_asked_nodes = remove_nth_item(graph_for_reference.nodes, len(x)-1)
        rollback_affected_nodes = remove_sublist(graph_for_reference.nodes, previously_affected_nodes)
        all_nodes_without_last = remove_nth_item(graph_for_reference.nodes, len(x)-1)
        query = find_max_d_con(rollback_asked_nodes, rollback_affected_nodes, all_nodes_without_last)
        return tactical_loop(current_asked, current_evidence, rollback_affected_nodes, new_snapshot, precision_list+[current_precision_list], stability_list+[current_stability_list])
    elif there_are_no_nodes_left and its_time_to_terminate:
        raise ThisIsImpossible
    elif there_are_nodes_left and not_yet_time_to_terminate:
        return tactical_loop(current_asked, current_evidence, updated_nodes, new_snapshot, precision_list+[current_precision_list], stability_list+[current_stability_list])
    elif there_are_nodes_left and its_time_to_terminate:
        return prev_snapshot, precision_list, stability_list


def forall(unary_pred, collection):
    return reduce(lambda acc, elem: unary_pred(elem) and acc, collection, True)


def find_max_d_con(current_asked, updated_nodes, list_of_all_node):  # 전체 node pool을 제한할 수 있음
    """graph_for_reference의 node들 중에서 가장 d_connected node가 가장 많은 노드를 찾아낸다."""
    tmpdict = dict()
    for node in list_of_all_node:
        tmpdict[node] = d_connected(node, current_asked)
    tmpdict = valmap(lambda set_: set_-set(current_asked)-set(updated_nodes), tmpdict)
    if forall(lambda set_: set_ == set(), tmpdict.values()):  # no more to ask
        return None
    tmpdict = valmap(lambda set_: len(set_), tmpdict)
    max_key = max(tmpdict, key=lambda key: tmpdict[key])
    return max_key


def first_rank_is_way_higher(parameters):
    first_rank = max(parameters)
    parameters_ = parameters[:]
    parameters_.remove(first_rank)
    second_rank = max(parameters_)
    if first_rank - second_rank < 0.1:
        return False
    else:
        return True


def time_to_terminate(BN, current_evidence):
    # the distribution across random variables' values
    dist_dicts = list(map(lambda dist: dist.parameters[0], BN_for_inference.predict_proba({})))
    # list of lists of the probabilities across random variables' values, extracted from dist_dicts
    dist_probs = list(map(lambda dist: list(dist.values()), dist_dicts))
    # Do all the nodes' probability lists satisfy first_rank_is_way_higher()?
    return reduce(lambda acc, lst: first_rank_is_way_higher(lst) and acc, dist_probs, True)


def tactical_loop_entry():
    pass


def tactical_loop(current_asked, current_evidence, updated_nodes, prev_snapshot, precision_list, stability_list):
    """the main interaction functionality, asking tactically using d-separation"""
    # node들 중에서, 가장 d_connected node가 많은 노드를 구한다.
    query = find_max_d_con(current_asked, updated_nodes)
    if not query:  # query가 비었음: 더 이상 물어볼 것이 없음
        print("nothing more to ask!")
        return prev_snapshot, precision_list, stability_list
    oracle_response = input("What label does <" + query + "> bear? [src/sin/san/non]: ")
    updated_nodes = updated_nodes + list(d_connected(query, current_asked))
    current_asked = current_asked + [query]
    if oracle_response == 'src':
        current_evidence[query] = 1
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(new_snapshot)
        current_precision_list = calculate_precision(new_snapshot)
        current_stability_list = calculate_stability(prev_snapshot, new_snapshot)
        return tactical_loop(current_asked, current_evidence, updated_nodes, new_snapshot, precision_list+[current_precision_list], stability_list+[current_stability_list])
    elif oracle_response == 'sin':
        current_evidence[query] = 2
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(new_snapshot)
        current_precision_list = calculate_precision(new_snapshot)
        current_stability_list = calculate_stability(prev_snapshot, new_snapshot)
        return tactical_loop(current_asked, current_evidence, updated_nodes, new_snapshot, precision_list+[current_precision_list], stability_list+[current_stability_list])
    elif oracle_response == 'san':
        current_evidence[query] = 3
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(new_snapshot)
        current_precision_list = calculate_precision(new_snapshot)
        current_stability_list = calculate_stability(prev_snapshot, new_snapshot)
        return tactical_loop(current_asked, current_evidence, updated_nodes, new_snapshot, precision_list+[current_precision_list], stability_list+[current_stability_list])
    elif oracle_response == 'non':
        current_evidence[query] = 4
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(new_snapshot)
        current_precision_list = calculate_precision(new_snapshot)
        current_stability_list = calculate_stability(prev_snapshot, new_snapshot)
        return tactical_loop(current_asked, current_evidence, updated_nodes, new_snapshot, precision_list+[current_precision_list], stability_list+[current_stability_list])


def single_loop(query):
    oracle_response = input("What label does <" + query + "> bear? [src/sin/san/non]: ")
    current_evidence = {}
    if oracle_response == 'src':
        current_evidence[query] = 1
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(new_snapshot)
    elif oracle_response == 'sin':
        current_evidence[query] = 2
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(new_snapshot)
    elif oracle_response == 'san':
        current_evidence[query] = 3
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(new_snapshot)
    elif oracle_response == 'non':
        current_evidence[query] = 4
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(new_snapshot)


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
        

def make_names_and_dists(snapshot):
    dists = []
    node_name_list = list(map(lambda node: node.name, BN_for_inference.states))
    for dist in snapshot:
        if type(dist) == int:  # oracle에 의해 고정된 경우!
            dists.append(normalize_dist(dist))
        else:
            dists.append(dist.parameters[0])
    names_and_dists = list(zip(node_name_list, dists))
    return names_and_dists


def visualize_snapshot(snapshot):
    """한번 iteration 돌 때마다, 전체 BN의 snapshot을 가시화한다."""
    plt.clf()
    names_and_dists = make_names_and_dists(snapshot)
    names_and_labels = list(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists))
    colormap = create_colormap(names_and_labels)
    nx.draw(graph_for_reference, node_color=colormap,
            pos=nx.circular_layout(graph_for_reference),
            with_labels=True, node_size=100)
    plt.show()


def report_results(final_snapshot):
    initial_snapshot = BN_for_inference.predict_proba({})
    names_and_dists_initial = make_names_and_dists(initial_snapshot)
    names_and_labels_initial = list(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists_initial))

    names_and_dists_final = make_names_and_dists(final_snapshot)
    names_and_labels_final = list(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists_final))
    
    changed_mesg = []
    for tup1, tup2 in zip(names_and_labels_initial, names_and_labels_final):
        # if the label has changed after interaction
        if tup1[1] != tup2[1]:
            print(tup1[0]+" is updated from "+tup1[1]+" to "+tup2[1])


def save_data_as_csv(final_snapshot):
    """inference가 다 끝난 label들을 csv로 저장한다."""
    names_and_dists_final = make_names_and_dists(final_snapshot)
    names_and_labels_final = list(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists_final))
    out_df = pd.DataFrame(names_and_labels_final, columns=["name", "label"])
    out_df.to_csv("inferred.csv", mode='w')
        

def report_meta_statistics():
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


# Methods for Scoring ====================================
# ========================================================

correct_solution = dict([('void PrintStream.println(int)', 'sin'),
                         ('void WhatIWantExample.g(int)', 'san'),
                         ('void WhatIWantExample.m3(int)', 'sin'),
                         ('void WhatIWantExample.h(int)', 'non'),
                         ('void WhatIWantExample.main()', 'non'),
                         ('int WhatIWantExample.m2(int)', 'san'),
                         ('void WhatIWantExample.f()', 'src'),
                         ('int WhatIWantExample.m1()', 'src')])


def calculate_precision(current_snapshot):
    """현재 확률분포 스냅샷의 정확도를 측정한다."""
    # current_snapshot의 타입은? np.ndarray of Distribution.
    names_and_dists = make_names_and_dists(current_snapshot)
    names_and_labels = dict(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists))
    wrong_nodes = []
    for node_name in graph_for_reference.nodes:
        if names_and_labels[node_name] == correct_solution[node_name]:
            wrong_nodes.append(node_name)
    return wrong_nodes


# time t에서의 stability: time (t-1)에서의 스냅샷과 비교했을 때 time t에서의 스냅샷에서 레이블이 달라진 노드의 개수
def calculate_stability(prev_snapshot, current_snapshot):
    """직전 확률분포 스냅샷에 대한 현재 확률분포 스냅샷의 stability를 측정한다."""
    names_and_dists_prev = make_names_and_dists(prev_snapshot)
    names_and_labels_prev = dict(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists_prev))
    names_and_dists_current = make_names_and_dists(current_snapshot)
    names_and_labels_current = dict(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists_current))
    changed_nodes = []
    for node_name in graph_for_reference.nodes:
        if names_and_labels_prev[node_name] != names_and_labels_current[node_name]:
            changed_nodes.append(node_name)
    return changed_nodes


def build_graph(result_report):
    """precision_graph의 x축 값의 list와 y축 값의 list를 만든다."""
    x = list(range(1, len(graph_for_reference.nodes)+1))
    y = []
    for elem_list in result_report:
        number_of_elem_nodes = len(elem_list)
        y.append(number_of_elem_nodes)
    return x, y


# for generating fresh variables
precision_figure_number = 1
stability_figure_number = 1


def draw_report_graph(x, y):
    """precision graph, stability graph를 모두 그릴 수 있는 다재다능한 함수. NOTE: x와 y의 input 길이를 맞춰줘야 함."""
    global precision_figure_number
    plt.clf()
    plt.figure(precision_figure_number)
    precision_figure_number += 1
    plt.plot(x, y, 'b-')
    plt.axis([1, 8, 0, 8])
    plt.ion()
    plt.show(block=False)


# ========================================================


def main():
    initial_snapshot = BN_for_inference.predict_proba({})
    # final_snapshot, precision_list, stability_list = tactical_loop(list(), dict(), list(), initial_snapshot, list(), list())
    final_snapshot, precision_list, stability_list = random_loop(list(), dict(), initial_snapshot, list(), list())
    report_results(final_snapshot)
    save_data_as_csv(final_snapshot)
    draw_report_graph(*build_graph(precision_list))
    draw_report_graph(*build_graph(stability_list))


raw_data.close()
edges_data.close()


if __name__ == "__main__":
    main()
