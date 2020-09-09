from pomegranate import *
import time
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as ptch
import matplotlib.axes as axes
import pandas as pd
import csv
import networkx as nx
import itertools as it
import os
import random
import make_BN

from solutions import *
from scrape_oracle_docs import *
from toolz import valmap
from matplotlib.ticker import MaxNLocator
from create_node import process
from make_underlying_graph import find_edge_labels, df_reader, call_reader
from make_CPT import *


# Constants ========================================
# ==================================================

graph_for_reference = nx.read_gpickle("sagan_site_graph")
df_edges = df_reader()
call_edges = call_reader()

# Exceptions ========================================
# ===================================================

class ThisIsImpossible(Exception):
    pass

class TooManyEdges(Exception):
    pass


# simple loops ============================================
# ========================================================

def random_loop(BN_for_inference, graph_for_reference, current_asked, current_evidence, prev_snapshot, precision_list, stability_list):
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
        # snapshot은 distribution object들의 nparray이다.
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(graph_for_reference, new_snapshot, [])
        current_precision_list = calculate_precision(new_snapshot)
        current_stability_list = calculate_stability(prev_snapshot, new_snapshot)
        return random_loop(BN_for_inference, graph_for_reference, current_asked+[query], current_evidence, new_snapshot,  precision_list+[current_precision_list], stability_list+[current_stability_list])
    elif oracle_response == 'sin':
        current_evidence[query] = 2
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(graph_for_reference, new_snapshot, [])
        current_precision_list = calculate_precision(new_snapshot)
        current_stability_list = calculate_stability(prev_snapshot, new_snapshot)
        return random_loop(BN_for_inference, graph_for_reference, current_asked+[query], current_evidence, new_snapshot,  precision_list+[current_precision_list], stability_list+[current_stability_list])
    elif oracle_response == 'san':
        current_evidence[query] = 3
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(graph_for_reference, new_snapshot, [])
        current_precision_list = calculate_precision(new_snapshot)
        current_stability_list = calculate_stability(prev_snapshot, new_snapshot)
        return random_loop(BN_for_inference, graph_for_reference, current_asked+[query], current_evidence, new_snapshot,  precision_list+[current_precision_list], stability_list+[current_stability_list])
    elif oracle_response == 'non':
        current_evidence[query] = 4
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(graph_for_reference, new_snapshot, [])
        current_precision_list = calculate_precision(new_snapshot)
        current_stability_list = calculate_stability(prev_snapshot, new_snapshot)
        return random_loop(BN_for_inference, graph_for_reference, current_asked+[query], current_evidence, new_snapshot,  precision_list+[current_precision_list], stability_list+[current_stability_list])

    
def single_loop(query):
    oracle_response = input("What label does <" + query + "> bear? [src/sin/san/non]: ")
    current_evidence = {}
    if oracle_response == 'src':
        current_evidence[query] = 1
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(graph_for_reference, new_snapshot, [])
    elif oracle_response == 'sin':
        current_evidence[query] = 2
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(graph_for_reference, new_snapshot, [])
    elif oracle_response == 'san':
        current_evidence[query] = 3
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(graph_for_reference, new_snapshot, [])
    elif oracle_response == 'non':
        current_evidence[query] = 4
        new_snapshot = BN_for_inference.predict_proba(current_evidence)
        visualize_snapshot(graph_for_reference, new_snapshot, [])



# tactical loop and its calculations ====================
# ========================================================

def tactical_loop(graph_for_reference, interaction_number, current_asked, current_evidence, updated_nodes, prev_snapshot, precision_list, stability_list, precision_inferred_list, **config):
    """the main interaction functionality (loops via recursion), asking tactically using d-separation
       parameters:
            - interaction_number: number of interactions performed so far.
            - current_asked: names of currently asked nodes.
            - current_evidence: dict of given evidences accumulated so far
            - updated_nodes: updated nodes which are currently being tracked of
            - prev_snapshot: snapshot from the previous call
            - precision_list: accumulated precision values
            - stability_list: accumulated stability values
       available config:
            - skip_call_sim_heur (bool): skip an interaction for non methods connected with call/sim edges.
    """
    # some variables to make our code resemble English
    if config["skip_call_sim_heur"]:  # now we prune the pool with non_nodes_to_skip
        pruneable_nodes = non_nodes_to_skip(graph_for_reference.nodes)
        there_are_nodes_left = find_max_d_con(graph_fore_reference, current_asked, updated_nodes, graph_for_reference.nodes, prune=pruneable_nodes, nth=0)
        there_are_nodes_left = there_are_nodes_left
        there_are_no_nodes_left = not there_are_nodes_left
        its_time_to_terminate = time_to_terminate(BN_for_inference, current_evidence)
        not_yet_time_to_terminate = not its_time_to_terminate

        maybe_query_tuple = there_are_nodes_left
        if maybe_query_tuple == None:
            query = None
            dependent_nodes = []
        else:
            query = maybe_query_tuple[0]
            dependent_nodes = maybe_query_tuple[1]
            # i = 0
            # while query in pruneable_nodes:
            #     query, dependent_nodes = find_max_d_con(graph_for_reference, current_asked, updated_nodes, graph_for_reference.nodes, prune=pruneable_nodes, nth=i)
            #     i += 1
    else:  # vanilla
        print("1")
        there_are_nodes_left = find_max_d_con(graph_for_reference, current_asked, updated_nodes, graph_for_reference.nodes, nth=0)
        print("2")
        there_are_no_nodes_left = not there_are_nodes_left
        print("3")
        its_time_to_terminate = time_to_terminate(BN_for_inference, current_evidence)
        print("4")
        not_yet_time_to_terminate = not its_time_to_terminate
        print("5")

        maybe_query_tuple = find_max_d_con(graph_for_reference, current_asked, updated_nodes, graph_for_reference.nodes, nth=0)
        print("6")
        if maybe_query_tuple == None:
            query = None
            dependent_nodes = []
        else:
            query = maybe_query_tuple[0]
            dependent_nodes = maybe_query_tuple[1]

    if there_are_no_nodes_left and not_yet_time_to_terminate:
        if set(graph_for_reference.nodes) == set(current_asked):
            print("\nWarning: some distributions are not fully determined.\n")
            return prev_snapshot, precision_list, stability_list
        else:
            if config["skip_call_sim_heur"]:
                query, dependent_nodes = find_max_d_con(graph_for_reference, [], [], remove_sublist(graph_for_reference.nodes, current_asked), nth=0, prune=pruneable_nodes)
            else: # vanilla
                query, dependent_nodes = find_max_d_con(graph_for_reference, [], [], remove_sublist(graph_for_reference.nodes, current_asked), nth=0)
    elif there_are_no_nodes_left and its_time_to_terminate:
        return prev_snapshot, precision_list, stability_list
    elif there_are_nodes_left and not_yet_time_to_terminate:
        pass
    elif there_are_nodes_left and its_time_to_terminate:
        raise ThisIsImpossible

    oracle_response = input("What label does <" + query + "> bear? [src/sin/san/non]: ")
    updated_nodes = updated_nodes + list(d_connected(graph_for_reference, query, current_asked, graph_for_reference.nodes))
    current_asked = current_asked + [query]
    if oracle_response == 'src':
        current_evidence[query] = 1
    elif oracle_response == 'sin':
        current_evidence[query] = 2
    elif oracle_response == 'san':
        current_evidence[query] = 3
    elif oracle_response == 'non':
        current_evidence[query] = 4
    new_snapshot = BN_for_inference.predict_proba(current_evidence)
    current_precision = calculate_precision(new_snapshot)
    current_stability = calculate_stability(prev_snapshot, new_snapshot)
    current_precision_inferred = calculate_precision_inferred(new_snapshot, interaction_number)
    precision_list[interaction_number] = current_precision
    stability_list[interaction_number] = current_stability
    precision_inferred_list[interaction_number] = current_precision_inferred
    draw_precision_graph(list(range(1, len(BN_for_inference.states)+1)), precision_list)
    draw_stability_graph(list(range(1, len(BN_for_inference.states)+1)), stability_list)
    draw_precision_inferred_graph(range(1, len(BN_for_inference.states)+1), precision_inferred_list)
    visualize_snapshot(graph_for_reference, new_snapshot, dependent_nodes)
    plt.show(block=False)
    return tactical_loop(graph_for_reference, interaction_number+1, current_asked, current_evidence, updated_nodes, new_snapshot, precision_list, stability_list, precision_inferred_list, **config)


def d_connected(graph_for_reference, node, current_asked, pool):
    """현재까지 물어본 노드들이 주어졌을 때, node와 조건부 독립인 노드들의 set을 찾아낸다. Complexity: O(n)."""
    out = set()
    print(len(graph_for_reference.nodes))
    for other_node in graph_for_reference.nodes:
        # print("가")
        if nx.d_separated(graph_for_reference, {node}, {other_node}, set(current_asked)):
            out.add(other_node)
    return set(graph_for_reference.nodes) - out


def remove_sublist(lst, sublst):
    """remove the sublst from lst without any side-effect."""
    out = []
    for elem in lst:
        if elem not in sublst:
            out.append(elem)
    return out


def forall(unary_pred, collection):
    return reduce(lambda acc, elem: unary_pred(elem) and acc, collection, True)


def non_nodes_to_skip(snapshot):
    """현재 스냅샷으로 계산된 names_and_labels를 받아서, 다음을 만족하는 노드 n을 모은다:
       n과 연결된 이웃 (parent 혹은 child)이
         1. non으로 고정되었고,
         2. 맞고 있는/쏘고 있는 화살표가 non/sim밖에 없다."""
    can_be_excluded = []
    for node_name in graph_for_reference.nodes:
        parents = graph_for_reference.predecessors(node_name)
        children = graph_for_reference.successors(node_name)
        from_parents_edges = []
        to_children_edges = []
        for parent in parents:
            from_parents_edges.append((parent, node_name))
        for child in children:
            to_children_edges.append((node_name, child))
        # 이제 엣지의 레이블을 포착해야 한다.
        if forall(lambda edge: edge not in df_edges, from_parents_edges) and\
           forall(lambda edge: edge not in df_edges, to_children_edges):
            can_be_excluded.append(node_name)
    return set(can_be_excluded)


def find_max_d_con(graph_for_reference, current_asked, updated_nodes, list_of_all_node, **kwargs):  # 전체 node pool을 제한할 수 있음
    """graph_for_reference의 node들 중에서 가장 d_connected node가 가장 많은 노드를 찾아낸다."""
    d_connected_set_dict = dict()
    print("a")
    for node in list_of_all_node:
        d_connected_set_dict[node] = d_connected(graph_for_reference, node, current_asked, list_of_all_node)
    d_connected_set_dict = valmap(lambda set_: set_-set(current_asked)-set(updated_nodes), d_connected_set_dict)
    print("b")
    if forall(lambda set_: set_ == set(), d_connected_set_dict.values()):  # no more to ask
        return None
    d_connected_len_dict = valmap(lambda set_: len(set_), d_connected_set_dict)
    nth = kwargs['nth']
    # print("nth:", nth)
    # dictionary에서 value만을 추출해 내림차순으로 정렬한다.
    print("b")
    if 'prune' in kwargs.keys():
        to_prune = kwargs['prune']
        number_of_sets_sorted = list(set(d_connected_len_dict.values()))  # not yet sorted..
        number_of_sets_sorted.sort(reverse=True)  # now sorted!
        nth_largest_node_names = []
        nth_largest_cardinality = number_of_sets_sorted[nth]
        # print("nth_largest_cardinality:", nth_largest_cardinality)
        # print("d_connected_len_dict:", d_connected_len_dict)

        for node_name, cardinality in d_connected_len_dict.items():
            if nth_largest_cardinality == cardinality and\
               node_name not in current_asked and\
               node_name not in to_prune:
                nth_largest_node_names.append(node_name)
        # print("nth_largest_node_names:",  nth_largest_node_names)
        if nth_largest_node_names == []:
            while nth_largest_node_names == []:
                number_of_sets_sorted.remove(number_of_sets_sorted[0])
                nth_largest_cardinality = number_of_sets_sorted[nth]
                # print("nth_largest_cardinality:", nth_largest_cardinality)
                for node_name, cardinality in d_connected_len_dict.items():
                    if nth_largest_cardinality == cardinality and\
                       node_name not in current_asked and\
                       node_name not in to_prune:
                        nth_largest_node_names.append(node_name)
                if nth_largest_node_names == []:
                    for node_name, cardinality in d_connected_len_dict.items():
                        if nth_largest_cardinality == cardinality and\
                           node_name not in current_asked:
                            nth_largest_node_names.append(node_name)
        out = nth_largest_node_names[0]
        return out, d_connected_set_dict[out]
    else:
        max_key = max(d_connected_len_dict, key=lambda key: d_connected_len_dict[key])
        return max_key, d_connected_set_dict[max_key]


def is_confident(parameters):
    """확률분포 (Distribution 오브젝트의 parameters 부분)를 보고, 가장 높은 확률이 다른 확률들보다 적어도 0.1은 높은지 확인한다."""
    if type(parameters) == dict:
        parameters = list(parameters.values())
    first_rank = max(parameters)
    parameters_ = parameters[:]
    parameters_.remove(first_rank)
    second_rank = max(parameters_)
    if first_rank - second_rank < 0.05:
        return False
    else:
        return True


def time_to_terminate(BN, current_evidence):
    # the distribution across random variables' values
    names_and_params = make_names_and_params(BN_for_inference.predict_proba(current_evidence))
    params = list(map(lambda tup: tup[1], names_and_params))
    # list of lists of the probabilities across random variables' values, extracted from dist_dicts
    dist_probs = list(map(lambda dist: list(dist.values()), params))
    # Do all the nodes' probability lists satisfy is_confident()?
    return reduce(lambda acc, lst: is_confident(lst) and acc, dist_probs, True)


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


# visualizing functions and their dependencies ============
# ========================================================

node_colordict = {"src": "red", "sin": "orange", "san": "yellow", "non": "green"}

def visualize_snapshot(graph_for_reference, snapshot, dependent_nodes):
    """한번 iteration 돌 때마다, 전체 BN의 snapshot을 가시화한다. 이 때, confident node들 위에는 `conf`라는 문구를 띄운다."""
    network_figure = plt.figure("Bayesian Network")
    network_figure.clf()
    plt.ion()
    ax = network_figure.add_subplot()
    names_and_params = make_names_and_params(snapshot)
    params = list(map(lambda tup: tup[1], names_and_params))
    names_and_labels = list(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_params))
    node_colormap = create_node_colormap(names_and_labels)
    edge_colormap = create_edge_colormap()

    node_posmap = nx.circular_layout(graph_for_reference)

    # confident node들 위에 문구 띄우기
    confident_node_indices = []
    for i, param in enumerate(params):
        if is_confident(param):
            confident_node_indices.append(i)
    confident_nodes = list(map(lambda index: names_and_params[index][0], confident_node_indices))
    for confident_node in confident_nodes:
        x, y = node_posmap[confident_node]
        plt.text(x, y+0.1, s='conf', bbox=dict(facecolor='blue', alpha=0.5), horizontalalignment='center')
    
    # dependent node들 다각형으로 그리기
    coord_lists = []
    for dependent_node in dependent_nodes:
        coord_lists.append(node_posmap[dependent_node])
    coord_lists = np.asarray(coord_lists)
    # polygon = ptch.Polygon(coord_lists, closed=True, alpha=0.4)
    # ax.add_patch(polygon)

    nx.draw(graph_for_reference,
            node_color=node_colormap, edge_color=edge_colormap,
            pos=node_posmap,
            ax=ax,
            with_labels=True, node_size=100)


def draw_precision_graph(x, y):
    """precision graph를 그리는 함수. NOTE: x와 y의 input 길이를 맞춰줘야 함."""
    plt.ion()
    precision_figure = plt.figure("Precision")
    ax = precision_figure.gca()
    ax.xaxis.set_major_locator(MaxNLocator(integer=True))
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    precision_figure.clf()
    num_of_states = len(graph_for_reference.nodes)
    plt.xlim(1, num_of_states)
    plt.ylim(0, num_of_states)
    plt.xlabel('# of interactions')
    plt.ylabel('# of correct nodes')
    plt.title("Precision development during interaction")
    plt.plot(x, y, 'b-')
    # precision_figure.add_axes([1, num_of_states, 0, num_of_states])
    precision_figure.canvas.draw()


def draw_stability_graph(graph_for_reference, x, y):
    """stability graph를 그리는 함수. NOTE: x와 y의 input 길이를 맞춰줘야 함."""
    plt.ion()
    stability_figure = plt.figure("Stability")
    ax = stability_figure.gca()
    ax.xaxis.set_major_locator(MaxNLocator(integer=True))
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    stability_figure.clf()
    num_of_states = len(graph_for_reference.nodes)
    plt.xlim(1, num_of_states)
    plt.ylim(0, num_of_states)
    plt.xlabel("# of interactions")
    plt.ylabel('# of changed nodes')
    plt.title("Stability development during interaction")
    plt.plot(x, y, 'b-')
    # stability_figure.add_axes([1, num_of_states, 0, num_of_states])
    stability_figure.canvas.draw()


def draw_precision_inferred_graph(graph_for_reference, x, y):
    """stability graph를 그리는 함수. NOTE: x와 y의 input 길이를 맞춰줘야 함."""
    plt.ion()
    stability_figure = plt.figure("Inferred Precision")
    ax = stability_figure.gca()
    ax.xaxis.set_major_locator(MaxNLocator(integer=True))
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    stability_figure.clf()
    num_of_states = len(graph_for_reference.nodes)
    plt.xlim(1, num_of_states)
    plt.ylim(0, num_of_states)
    plt.xlabel("# of interactions")
    plt.ylabel('# of correctly inferred nodes')
    plt.title("Inferred precision development during interaction")
    plt.plot(x, y, 'b-')
    # stability_figure.add_axes([1, num_of_states, 0, num_of_states])
    stability_figure.canvas.draw()


def create_node_colormap(names_and_labels):
    """BN을 기준으로 계산된 names_and_labels를 받아서 graph_for_reference를 기준으로 한 colormap을 만든다."""
    out = list(graph_for_reference.nodes)[:]
    for name, label in names_and_labels:
        index = out.index(name)
        out[index] = node_colordict[label]
    return out


def create_edge_colormap():
    """엣지 목록을 받아서, 엣지의 종류에 따라 graph_for_reference를 그릴 때 엣지의 색깔을 달리한다."""
    out = list(graph_for_reference.edges)[:]
    for edge in out:
        index = out.index(edge)
        if edge in df_edges:    # df
            out[index] = "red"
        elif edge in call_edges:  # call
            out[index] = "green"
        else:                   # sim
            out[index] = "blue"
    return out


def make_names_and_params(snapshot):
    """snapshot을 읽어서, 랜덤변수 별 확률값의 dict인 parameters만을 빼낸 다음 node의 이름과 짝지어서 list에 담아 낸다."""
    dists = []
    node_name_list = list(graph_for_reference.nodes)
    for dist in snapshot:
        if type(dist) == int:  # oracle에 의해 고정된 경우!
            dists.append(normalize_dist(dist))
        else:
            dists.append(dist.parameters[0])
    names_and_params = list(zip(node_name_list, dists))
    return names_and_params


def report_results(BN_for_inference, final_snapshot):
    initial_snapshot = BN_for_inference.predict_proba({})
    names_and_dists_initial = make_names_and_params(initial_snapshot)
    names_and_labels_initial = list(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists_initial))

    names_and_dists_final = make_names_and_params(final_snapshot)
    names_and_labels_final = list(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists_final))
    
    changed_mesg = []
    for tup1, tup2 in zip(names_and_labels_initial, names_and_labels_final):
        # if the label has changed after interaction
        if tup1[1] != tup2[1]:
            print(tup1[0]+" is updated from "+tup1[1]+" to "+tup2[1])


def save_data_as_csv(final_snapshot):
    """inference가 다 끝난 label들을 csv로 저장한다."""
    names_and_dists_final = make_names_and_params(final_snapshot)
    names_and_labels_final = list(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists_final))
    out_df = pd.DataFrame(names_and_labels_final, columns=["name", "label"])
    out_df.to_csv("inferred.csv", mode='w')
        

def report_meta_statistics(graph_for_reference, BN_for_inference):
    """meta-functionality for debugging"""
    print("# of nodes: ", len(list(BN_for_inference.states)))
    print("# of edges: ", len(list(BN_for_inference.edges)))
    nodes = list(graph_for_reference.nodes)
    max_num_of_in_edges = max(list(map(lambda node: graph_for_reference.in_edges(nbunch=node), nodes)))
    max_num_of_out_edges = max(list(map(lambda node: graph_for_reference.out_edges(nbunch=node), nodes)))
    print("maximum # of in-edges:", max_num_of_in_edges)
    print("maximum # of out-edges:", max_num_of_out_edges)
    print("elapsed time: ", time.time() - start)


# Methods for calculating graph values ====================
# ========================================================

def calculate_precision(current_snapshot):
    """현재 확률분포 스냅샷의 정확도를 측정한다."""
    # current_snapshot의 타입은? np.array of Distribution.
    names_and_params = make_names_and_params(current_snapshot)
    names_and_labels = dict(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_params))
    correct_nodes = []
    for node_name in graph_for_reference.nodes:
        if names_and_labels[node_name] == correct_solution_relational[node_name]:
            correct_nodes.append(node_name)
    return len(correct_nodes)


def calculate_stability(prev_snapshot, current_snapshot):
    """직전 확률분포 스냅샷에 대한 현재 확률분포 스냅샷의 stability를 측정한다.
       stability: time t에서의 stability: time (t-1)에서의 스냅샷과 비교했을 때 time t에서의 스냅샷에서 레이블이 달라진 노드의 개수."""
    names_and_dists_prev = make_names_and_params(prev_snapshot)
    names_and_labels_prev = dict(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists_prev))
    names_and_dists_current = make_names_and_params(current_snapshot)
    names_and_labels_current = dict(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists_current))
    changed_nodes = []
    for node_name in graph_for_reference.nodes:
        if names_and_labels_prev[node_name] != names_and_labels_current[node_name]:
            changed_nodes.append(node_name)
    return len(changed_nodes)


def calculate_precision_inferred(current_snapshot, number_of_interaction):
    """현재 확률분포 스냅샷을 보고, BN이 순수하게 infer한 것들 중에 맞힌 레이블의 개수를 구한다."""
    # current_snapshot의 타입은? np.array of Distribution.
    names_and_params = make_names_and_params(current_snapshot)
    names_and_labels = dict(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_params))
    correct_nodes = []
    for node_name in graph_for_reference.nodes:
        if names_and_labels[node_name] == correct_solution_relational[node_name]:
            correct_nodes.append(node_name)
    return len(correct_nodes) - number_of_interaction


# main ====================================================
# ========================================================

def main():
    start = time.time()

    BN_for_inference = make_BN.main()

    initial_prediction_time = time.time()
    initial_snapshot = BN_for_inference.predict_proba({}, n_jobs=-1)
    print("initial predicition_time:", time.time() - initial_prediction_time)
    number_of_states = len(BN_for_inference.states)
    initial_precision_list = [np.nan for _ in range(len(BN_for_inference.states))]
    initial_stability_list = [np.nan for _ in range(len(BN_for_inference.states))]
    initial_precision_inferred_list = [np.nan for _ in range(len(BN_for_inference.states))]
    print()  # for aesthetics in the REPL
    # final_snapshot, precision_list, stability_list = tactical_loop(graph_for_reference, 0, list(), dict(), list(), initial_snapshot, initial_precision_list, initial_stability_list, initial_precision_inferred_list, skip_call_sim_heur=False)
    final_snapshot, precision_list, stability_list = random_loop(BN_for_inference, graph_for_reference, list(), dict(), initial_snapshot, list(), list())
    report_results(initial_snapshot, final_snapshot)
    # save_data_as_csv(final_snapshot)

    raw_data.close()
    edges_data.close()
