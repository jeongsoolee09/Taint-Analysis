import csv
import json
import os.path
import random
import time
import argparse
import re
import make_BN
import matplotlib.pyplot as plt
import modin.pandas as pd
import networkx as nx
import numpy as np
import transfer_knowledge

from datetime import datetime
from matplotlib.ticker import MaxNLocator
from functools import reduce
from copy import deepcopy

from traceback_with_variables import activate_in_ipython_by_import, printing_exc


# Constants ========================================
# ==================================================


parser = argparse.ArgumentParser()
parser.add_argument("solution_file", help="path to the solution file. input 'None' if you don't have any.",
                    type=str)
args = parser.parse_args()

def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]

PROJECT_ROOT_DIR = retrieve_path()

if args.solution_file != "None" or args.solution_file != "none":
    with open(args.solution_file, "r+") as solution_file:
        SOLUTION = json.load(solution_file)
else:
    SOLUTION = None

NOW = datetime.now().strftime("%Y-%m-%d-%H:%M:%S")

def no_reflexive(relation):
    return list(filter(lambda tup: tup[0] != tup[1], relation))

df_data = open("df.csv", "r+")
df_reader = csv.reader(df_data)

call_data = open("callg.csv", "r+")
call_reader = csv.reader(call_data)

sim_data = open("pairwise_sims.csv", "r+")
sim_reader = csv.reader(sim_data)

DF_EDGES = no_reflexive(map(lambda lst: (lst[5], lst[10]), list(df_reader)[1:]))
CALL_EDGES = no_reflexive(map(lambda lst: (lst[5], lst[10]), list(call_reader)[1:]))
SIM_EDGES = no_reflexive(map(lambda lst: (lst[5], lst[10]), list(sim_reader)[1:]))

WINDOW_SIZE = 4

with open(PROJECT_ROOT_DIR+"skip_func.txt", "r+") as skip_func:
    skip_funcs = skip_func.readlines()
    skip_funcs = list(map(lambda string: string.rstrip(), skip_funcs))


PAIRWISE_SIMS = pd.read_csv("pairwise_sims.csv", index_col=0)
VERY_SIMILAR = PAIRWISE_SIMS[PAIRWISE_SIMS["score"] > 20][["id1", "id2"]]


# Random loop ========================================
# ====================================================


def random_loop(global_precision_list, snapshot_dict, graph_for_reference, BN_for_inference,
                  BN_for_inference_x, interaction_number, current_asked, current_evidence,
                  current_evidence_x, updated_nodes, prev_snapshot, prev_snapshot_x, precision_list, stability_list,
                  precision_inferred_list, loop_time_list, window, graph_file):
    """The main interaction functionality, asking randomly
       Parameters:
            - BN_for_inference: the Bayesian Network.
            - graph_for_reference: the underlying graph.
            - interaction_number: number of interactions performed so far.
            - current_asked: names of currently asked nodes.
            - current_evidence: dict of given evidences accumulated so far
            - prev_snapshot: snapshot from the previous call
            - precision_list: accumulated precision values
            - stability_list: accumulated stability values
            - precision_inferred_list: accumulated precision values purely inferred by the BN
            - loop_time_list: accumulated times took in belief propagation
            - window: sliding window with size 4"""

    loop_start = time.time()


    state_names = list(map(lambda node: node.name, BN_for_inference.states))
    APIs = list(filter(lambda node: node in skip_funcs, state_names))

    num_of_states = len(state_names)
    num_of_APIs = len(APIs)

    random_index = random.randint(0, len(APIs)-1)
    num_of_states = len(state_names)
    query = APIs[random_index]
    while query in current_asked:
        if set(current_asked) == set(APIs):
            break
        random_index = random.randint(0, len(APIs)-1)
        query = APIs[random_index]

    # some variables to make our code resemble English
    there_are_nodes_left = find_max_d_con(graph_for_reference, BN_for_inference, current_asked,
                                          updated_nodes, APIs)
    there_are_no_nodes_left = not there_are_nodes_left
    its_time_to_terminate = time_to_terminate(BN_for_inference, current_evidence, window, criteria='plateau')
    not_yet_time_to_terminate = not its_time_to_terminate

    # pick a method to ask by finding one with the maximum number of D-connected nodes
    if there_are_no_nodes_left:
        query = None
        dependent_nodes = []
    else:
        dependent_nodes = there_are_nodes_left[1]

    # exit the function based on various termination measures.
    if there_are_no_nodes_left and not_yet_time_to_terminate:
        print("Early termination: ran out of nodes")
        return (prev_snapshot, precision_list, stability_list,
                precision_inferred_list, loop_time_list, current_asked,
                global_precision_list)
    elif there_are_no_nodes_left and its_time_to_terminate:
        return (prev_snapshot, precision_list, stability_list,
                precision_inferred_list, loop_time_list, current_asked,
                global_precision_list)
    elif there_are_nodes_left and not_yet_time_to_terminate:
        pass
    elif there_are_nodes_left and its_time_to_terminate:
        save_data_as_csv(APIs, prev_snapshot)
        return (prev_snapshot, precision_list, stability_list,
                precision_inferred_list, loop_time_list, current_asked,
                global_precision_list)
    # exit the function based on confidence.
    if its_time_to_terminate:
        save_data_as_csv(prev_snapshot, state_names)
        return (prev_snapshot, precision_list, stability_list,
                precision_inferred_list, current_asked, global_precision_list)

    oracle_response = SOLUTION[query]
    updated_nodes += list(d_connected(graph_for_reference, BN_for_inference,
                                      query, current_asked, APIs))

    if oracle_response == 'src':
        current_evidence[query] = 1
    elif oracle_response == 'sin':
        current_evidence[query] = 2
    elif oracle_response == 'san':
        current_evidence[query] = 3
    elif oracle_response == 'non':
        current_evidence[query] = 4

    print("query:", query)
    print("current_evidence[query]:", current_evidence[query])

    current_asked.append(query)

    # the new snapshot after the observation and its inference time
    new_raw_snapshot = BN_for_inference.predict_proba(current_evidence, n_jobs=-1)
    new_snapshot = make_names_and_params(state_names, new_raw_snapshot)

    get_interaction_diff(query, prev_snapshot, new_snapshot)

    # update the snapshot_dict
    snapshot_dict[graph_file] = new_snapshot
    global_precision = evaluate_global_precision(snapshot_dict)
    global_precision_list.append(global_precision)

    # the new precision after the observation
    current_precision = calculate_precision(APIs, new_snapshot)
    precision_list[interaction_number] = current_precision

    # the new stability after the observation
    current_stability = calculate_stability(APIs, prev_snapshot, new_snapshot)
    stability_list[interaction_number] = current_stability

    # the new precision purely inferred by the BN, after the observation
    current_precision_inferred = calculate_precision_inferred(APIs, new_snapshot, interaction_number)
    precision_inferred_list[interaction_number] = current_precision_inferred

    # slide the window
    window = window[1:]          # dequeue the oldest one
    window.append(new_snapshot)  # and enqueue the newest one

    print(interaction_number, ":", (current_precision/len(APIs))*100, "%")

    # record this loop's looping time
    loop_time_list.append(time.time()-loop_start)

    # loop!
    return random_loop(global_precision_list, snapshot_dict, graph_for_reference, BN_for_inference,
                         BN_for_inference_x, interaction_number+1, current_asked, current_evidence,
                         current_evidence_x, updated_nodes, new_snapshot, prev_snapshot_x, precision_list, stability_list,
                         precision_inferred_list, loop_time_list, window, graph_file)


# Visualization Utils ====================================
# ========================================================


node_colordict = {"src": "red", "sin": "orange", "san": "yellow", "non": "green"}


def create_node_colormap(state_names, names_and_labels):
    """BN을 기준으로 계산된 names_and_labels를 받아서 graph_for_reference를 기준으로 한 colormap을 만든다."""
    out = list(state_names)[:]
    for name, label in names_and_labels:
        index = out.index(name)
        out[index] = node_colordict[label]
    return out


def create_edge_colormap(graph_for_reference):
    """엣지 목록을 받아서, 엣지의 종류에 따라 graph_for_reference를 그릴 때 엣지의 색깔을 달리한다."""
    edge_list = list(graph_for_reference.edges)[:]
    def mapfunc(edge):
        if edge in DF_EDGES:      # df
            return "red"
        elif edge in CALL_EDGES:  # call
            return "green"
        elif edge in SIM_EDGES:   # sim
            return "blue"
    mapped = list(map(mapfunc, edge_list))
    return mapped


def visualize_snapshot(state_names, graph_for_reference, snapshot, dependent_nodes):
    """한번 iteration 돌 때마다, 전체 BN의 snapshot을 가시화한다. 이 때, confident node들 위에는 `conf`라는 문구를 띄운다."""
    network_figure = plt.figure("Bayesian Network", figsize=(30, 15))
    network_figure.clf()
    ax = network_figure.add_subplot()
    params = list(map(lambda tup: tup[1], snapshot))
    names_and_labels = list(map(lambda tup: (tup[0], find_max_val(tup[1])), snapshot))
    node_colormap = create_node_colormap(state_names, names_and_labels)
    edge_colormap = create_edge_colormap(graph_for_reference)

    node_posmap = nx.circular_layout(graph_for_reference)

    # confident node들 위에 문구 띄우기
    confident_node_indices = []
    for i, param in enumerate(params):
        if is_confident(param):
            confident_node_indices.append(i)
    confident_nodes = list(map(lambda index: snapshot[index][0], confident_node_indices))
    for confident_node in confident_nodes:
        x, y = node_posmap[confident_node]
        plt.text(x, y+0.1, s='conf', bbox=dict(facecolor='blue', alpha=0.5), horizontalalignment='center')

    for node_name in list(graph_for_reference.nodes):
        if node_name not in state_names:
            graph_for_reference.remove_node(node_name)

    nx.draw(graph_for_reference,
            node_color=node_colormap,
            edge_color=edge_colormap,
            pos=node_posmap,
            ax=ax,
            with_labels=True, node_size=100)

    plt.show()


# tactical loop and its calculations =====================
# ========================================================


def tactical_loop(global_precision_list, snapshot_dict, graph_for_reference, BN_for_inference,
                  BN_for_inference_x, interaction_number, current_asked, current_evidence,
                  current_evidence_x, updated_nodes, prev_snapshot, prev_snapshot_x, precision_list, stability_list,
                  precision_inferred_list, loop_time_list, window, graph_file):
    """the main interaction functionality (loops via recursion), asking tactically using d-separation
       parameters:
            - graph_for_reference: the underlying graph.
            - interaction_number: number of interactions performed so far.
            - current_asked: names of currently asked nodes.
            - current_evidence: dict of given evidences accumulated so far
            - updated_nodes: updated nodes which are currently being tracked of
            - prev_snapshot: snapshot from the previous call
            - precision_list: accumulated precision values
            - stability_list: accumulated stability values
            - precision_inferred_list: accumulated precision values purely inferred by the BN
            - loop_time_list: accumulated times took in belief propagation
            - window: sliding window with size 4"""

    loop_start = time.time()

    state_names = list(map(lambda node: node.name, BN_for_inference.states))
    APIs = list(filter(lambda node: node in skip_funcs, state_names))

    num_of_states = len(state_names)
    num_of_APIs = len(APIs)

    # some variables to make our code resemble English
    there_are_nodes_left = find_max_d_con(graph_for_reference, BN_for_inference, current_asked,
                                          updated_nodes, APIs)
    there_are_no_nodes_left = not there_are_nodes_left
    its_time_to_terminate = time_to_terminate(BN_for_inference, current_evidence, window, criteria='plateau')
    not_yet_time_to_terminate = not its_time_to_terminate

    # pick a method to ask by finding one with the maximum number of D-connected nodes
    if there_are_no_nodes_left:
        query = None
        dependent_nodes = []
    else:
        query = there_are_nodes_left[0]
        dependent_nodes = there_are_nodes_left[1]

    # exit the function based on various termination measures.
    if there_are_no_nodes_left and not_yet_time_to_terminate:
        print("Early termination: ran out of nodes")
        return (prev_snapshot, prev_snapshot_x, precision_list, stability_list,
                precision_inferred_list, loop_time_list, current_asked,
                current_evidence, global_precision_list)
    elif there_are_no_nodes_left and its_time_to_terminate:
        return (prev_snapshot, prev_snapshot_x, precision_list, stability_list,
                precision_inferred_list, loop_time_list, current_asked,
                current_evidence, global_precision_list)
    elif there_are_nodes_left and not_yet_time_to_terminate:
        pass
    elif there_are_nodes_left and its_time_to_terminate:
        save_data_as_csv(APIs, prev_snapshot)
        return (prev_snapshot, prev_snapshot_x, precision_list, stability_list,
                precision_inferred_list, loop_time_list, current_asked,
                current_evidence, global_precision_list)

    # ask the chosen method and fetch the answer from the solutions
    oracle_response = SOLUTION[query]
    updated_nodes += list(d_connected(graph_for_reference, BN_for_inference,
                                      query, current_asked, APIs))

    if oracle_response == 'src':
        current_evidence[query] = 1
        current_evidence_x[query] = 1
    elif oracle_response == 'sin':
        current_evidence[query] = 2
        current_evidence_x[query] = 1
    elif oracle_response == 'san':
        current_evidence[query] = 3
        current_evidence_x[query] = 1
    elif oracle_response == 'non':
        current_evidence[query] = 4
        current_evidence_x[query] = 1

    print("query:", query)
    print("current_evidence[query]:", current_evidence[query])

    current_asked.append(query)

    # the new snapshot after the observation (with transferred knowledge)
    new_raw_snapshot = BN_for_inference.predict_proba(current_evidence, n_jobs=-1)
    new_snapshot = make_names_and_params(state_names, new_raw_snapshot)

    # # the new snapshot after the observation (without transferred knowledge)
    new_raw_snapshot_x = BN_for_inference_x.predict_proba(current_evidence_x, n_jobs=-1)
    new_snapshot_x = make_names_and_params(state_names, new_raw_snapshot_x)

    get_interaction_diff(query, prev_snapshot, new_snapshot)

    # visualize_snapshot(state_names, graph_for_reference, new_snapshot, dependent_nodes)

    # update the snapshot_dict
    snapshot_dict[graph_file] = new_snapshot
    global_precision = evaluate_global_precision(snapshot_dict)
    global_precision_list.append(global_precision)

    # the new precision after the observation
    current_precision = calculate_precision(APIs, new_snapshot)
    precision_list[interaction_number] = current_precision

    # the new stability after the observation
    current_stability = calculate_stability(APIs, prev_snapshot, new_snapshot)
    stability_list[interaction_number] = current_stability

    # the new precision purely inferred by the BN, after the observation
    current_precision_inferred = calculate_precision_inferred(APIs, new_snapshot, interaction_number)
    precision_inferred_list[interaction_number] = current_precision_inferred

    # slide the window
    window = window[1:]          # dequeue the oldest one
    window.append(new_snapshot)  # and enqueue the newest one

    print(interaction_number, ":", (current_precision/len(APIs))*100, "%")

    # record this loop's looping time
    loop_time_list.append(time.time()-loop_start)

    # loop!
    return tactical_loop(global_precision_list, snapshot_dict, graph_for_reference, BN_for_inference,
                         BN_for_inference_x, interaction_number+1, current_asked, current_evidence,
                         current_evidence_x, updated_nodes, new_snapshot, new_snapshot_x, precision_list, stability_list,
                         precision_inferred_list, loop_time_list, window, graph_file)


def d_connected(graph_for_reference, BN_for_inference, node, current_asked, pool):
    """현재까지 물어본 노드들이 주어졌을 때, node와 조건부 독립인 노드들의 set을 찾아낸다. Complexity: O(n)."""
    out = set()
    state_names = list(map(lambda node: node.name, BN_for_inference.states))
    for other_node in state_names:
        if nx.d_separated(graph_for_reference, {node}, {other_node}, set(current_asked)):
            out.add(other_node)
    return set(state_names) - out


def find_max_d_con(graph_for_reference, BN_for_inference,
                   current_asked, updated_nodes, list_of_all_nodes):
    """가장 d-connected 노드가 많은 노드를 리턴한다. 더 이상 고를 수 있는 노드가 없다면 None을 리턴한다."""
    node_dataframe = pd.DataFrame(list_of_all_nodes, columns=['nodes'])
    mapfunc = lambda row: len(d_connected(graph_for_reference, BN_for_inference,
                                          row['nodes'], current_asked,
                                          list_of_all_nodes)-set(current_asked)-set(updated_nodes))
    d_con_set_len = node_dataframe.apply(mapfunc, axis=1)
    if d_con_set_len.mask(d_con_set_len == 0).dropna().empty:
        return None
    node_dataframe["d_con_set_len"] = d_con_set_len
    node_dataframe.sort_values(by=["d_con_set_len"], inplace=True, ascending=False)
    return node_dataframe.iloc[0].nodes, node_dataframe.iloc[0].d_con_set_len


def is_confident(parameters):
    """확률분포 (Distribution 오브젝트의 parameters 부분)를 보고,
       가장 높은 확률이 다른 확률들보다 적어도 0.1은 높은지 확인한다."""
    if type(parameters) == dict:
        parameters = list(parameters.values())
    first_rank = max(parameters)
    parameters_ = parameters[:]
    parameters_.remove(first_rank)
    second_rank = max(parameters_)
    return first_rank - second_rank < 0.05


def time_to_terminate(BN_for_inference, current_evidence, window, **kwargs):
    """determine if it's time to terminate, based on different measures
       - Available kwargs:
           - 'plateau': terminate loop if the precision seems to be plateauing
           - 'confidence': terminate loop if all nodes' are confidently updated"""
    state_names = list(map(lambda node: node.name, BN_for_inference.states))
    if kwargs['criteria'] == 'confidence':
        # the distribution across random variables' values
        snapshot = BN_for_inference.predict_proba(current_evidence, n_jobs=-1)
        names_and_params = make_names_and_params(state_names, snapshot)
        params = list(map(lambda tup: tup[1], names_and_params))
        # list of lists of the probabilities across random variables' values, extracted from dist_dicts
        dist_probs = list(map(lambda distobj: list(distobj.values()), params))
        # Do all the nodes' probability lists satisfy is_confident()?
        return reduce(lambda acc, lst: is_confident(lst) and acc, dist_probs, True)
    elif kwargs['criteria'] == 'plateau':
        # take a look at the contents of the window
        acc = ()
        for snapshot in window:
            params = list(map(lambda tup: tup[1], snapshot))
            names_and_labels = list(map(lambda tup: (tup[0], find_max_val(tup[1])), snapshot))
            acc += (names_and_labels,)

        a, b, c, d = acc

        initial = np.ndarray([0])

        all_4_are_equal = np.array_equal(a, b) and np.array_equal(b, c) and np.array_equal(c, d)

        any_of_4_are_initial = np.array_equal(a, initial) or\
            np.array_equal(b, initial) or\
            np.array_equal(c, initial) or\
            np.array_equal(d, initial)

        there_is_a_pothole = (np.array_equal(a, c) and not np.array_equal(a, b) or\
                              np.array_equal(a, d) and not np.array_equal(c, d)) and\
                              not np.array_equal(a, initial) and\
                              not np.array_equal(c, initial) and\
                              not np.array_equal(d, initial)

        if all_4_are_equal and not any_of_4_are_initial:
            return True
        elif there_is_a_pothole:
            return True
        else:
            return False


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
# =========================================================


def draw_n_save(graph_file, BN_for_inference, precision_list, stability_list, precision_inferred_list, **kwargs):
    """available kwargs: random, tactical"""
    interaction_number = len(precision_list)

    state_names = list(map(lambda node: node.name, BN_for_inference.states))
    num_of_states = len(state_names)

    draw_precision_graph(graph_file, range(interaction_number),
                         precision_list, num_of_states, kwargs["loop_type"])
    draw_stability_graph(graph_file, range(interaction_number),
                         stability_list, num_of_states, kwargs["loop_type"])
    draw_precision_inferred_graph(graph_file, range(interaction_number),
                                  precision_inferred_list, num_of_states, kwargs["loop_type"])


def draw_precision_graph(graph_file, x, y, num_of_states, loop_type):
    """precision graph를 그리는 함수."""
    precision_figure = plt.figure("Precision")
    ax = precision_figure.gca()
    ax.xaxis.set_major_locator(MaxNLocator(integer=True))
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    precision_figure.clf()
    plt.xlim(1, num_of_states)
    plt.ylim(0, num_of_states)
    plt.xlabel('# of interactions')
    plt.ylabel('# of correct nodes')
    plt.title("Precision development during interaction ("+loop_type+")")
    plt.plot(x, y, 'b-')
    if not os.path.isdir(graph_file+"_stats"):
        os.mkdir(graph_file+"_stats")
    plt.savefig(graph_file+"_stats"+os.sep+\
                "precision_graph_"+NOW+"_"+loop_type+".png")


def draw_stability_graph(graph_file, x, y, num_of_states, loop_type):
    """stability graph를 그리는 함수."""
    stability_figure = plt.figure("Stability")
    ax = stability_figure.gca()
    ax.xaxis.set_major_locator(MaxNLocator(integer=True))
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    stability_figure.clf()
    plt.xlim(1, num_of_states)
    plt.ylim(0, num_of_states)
    plt.xlabel("# of interactions")
    plt.ylabel('# of changed nodes')
    plt.title("Stability development during interaction ("+loop_type+")")
    plt.plot(x, y, 'b-')
    if not os.path.isdir(graph_file+"_stats"):
        os.mkdir(graph_file+"_stats")
    plt.savefig(graph_file+"_stats"+os.sep+\
                "stability_graph_"+NOW+"_"+loop_type+".png")


def draw_precision_inferred_graph(graph_file, x, y, num_of_states, loop_type):
    """순수하게 BN이 추론해서 맞춘 노드의 개수에 대한 그래프를 그리는 함수."""
    precision_inferred_figure = plt.figure("Inferred Precision")
    ax = precision_inferred_figure.gca()
    ax.xaxis.set_major_locator(MaxNLocator(integer=True))
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    precision_inferred_figure.clf()
    plt.xlim(1, num_of_states)
    plt.ylim(0, num_of_states)
    plt.xlabel("# of interactions")
    plt.ylabel('# of correctly inferred nodes')
    plt.title("Inferred precision development during interaction ("+loop_type+")")
    plt.plot(x, y, 'b-')
    if not os.path.isdir(graph_file+"_stats"):
        os.mkdir(graph_file+"_stats")
    plt.savefig(graph_file+"_stats"+os.sep+\
                "precision_inferred_graph_"+NOW+"_"+loop_type+".png")


def make_names_and_params(state_names, snapshot):
    """snapshot을 읽어서, 랜덤변수 별 확률값의 dict인 parameters만을 빼낸 다음 node의 이름과 짝지어서 list에 담아 낸다."""
    distobjs = []
    for distobj in snapshot:
        if type(distobj) == int or type(distobj) == float:  # oracle에 의해 고정된 경우!
            distobjs.append(normalize_dist(distobj))
        else:
            distobjs.append(distobj.parameters[0])
    names_and_params = list(zip(state_names, distobjs))
    return names_and_params


def report_results(state_names, initial_snapshot, final_snapshot):
    names_and_dists_initial = make_names_and_params(state_names, initial_snapshot)
    names_and_labels_initial = list(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists_initial))

    names_and_dists_final = make_names_and_params(state_names, final_snapshot)
    names_and_labels_final = list(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_dists_final))

    for tup1, tup2 in zip(names_and_labels_initial, names_and_labels_final):
        # if the label has changed after interaction
        if tup1[1] != tup2[1]:
            print(tup1[0]+" is updated from "+tup1[1]+" to "+tup2[1])


def save_data_as_csv(state_names, final_snapshot):
    """inference가 다 끝난 label들을 csv로 저장한다."""
    names_and_labels_final = list(map(lambda tup: (tup[0], find_max_val(tup[1])), final_snapshot))
    out_df = pd.DataFrame(names_and_labels_final, columns=["name", "label"])
    out_df.to_csv("inferred.csv", mode='w')


def draw_n_save_global_precision_graph(global_precision_list):
    """precision graph를 그리는 함수."""
    precision_figure = plt.figure("Global Precision")
    ax = precision_figure.gca()
    ax.xaxis.set_major_locator(MaxNLocator(integer=True))
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    precision_figure.clf()
    plt.xlim(1, len(skip_funcs))
    plt.ylim(0, 100)
    plt.xlabel('# of interactions')
    plt.ylabel('% of correct nodes')
    plt.title("Global Precision development during interaction")
    plt.plot([x for x in range(len(skip_funcs))], global_precision_list, 'b-')
    plt.savefig("global_precision_graph_"+NOW+".png")


# Debugging Utilities =====================================
# =========================================================


def print_num_of_APIS(BN_for_inference):
    """Prints the number of API nodes present in the BN."""
    state_names = list(map(lambda node: node.name, BN_for_inference.states))
    APIs = list(filter(lambda node: node in skip_funcs, state_names))
    print("There are {} APIs in this BN".format(len(APIs)))


def get_interaction_diff(query, prev_snapshot, new_snapshot):
    prev_names_and_labels = dict(map(lambda tup: (tup[0], find_max_val(tup[1])), prev_snapshot))
    new_names_and_labels = dict(map(lambda tup: (tup[0], find_max_val(tup[1])), new_snapshot))

    nodes = prev_names_and_labels.keys()

    nodes_with_changed_labels = []

    for node in nodes:
        prev_label = prev_names_and_labels[node]
        new_label = new_names_and_labels[node]
        if prev_label != new_label and node != query:
            nodes_with_changed_labels.append((node, prev_label, new_label))

    acc = {}
    for node, prev_label, new_label in nodes_with_changed_labels:
        if node in skip_funcs:
            print("Node {} is updated from {} to {}".format(node, prev_label, new_label))
            acc[node] = dict(new_snapshot)[node]

    return acc


def report_meta_statistics(graph_for_reference, BN_for_inference):
    """meta-functionality for debugging"""
    print("# of nodes: ", len(list(BN_for_inference.states)))
    print("# of edges: ", len(list(BN_for_inference.edges)))

    state_names = list(map(lambda node: node.name, BN_for_inference.states))
    max_num_of_in_edges = max(list(map(lambda node: graph_for_reference.in_edges(nbunch=node), state_names)))
    max_num_of_out_edges = max(list(map(lambda node: graph_for_reference.out_edges(nbunch=node), state_names)))
    print("maximum # of in-edges:", max_num_of_in_edges)
    print("maximum # of out-edges:", max_num_of_out_edges)


# Methods for calculating graph values ====================
# =========================================================


def calculate_precision(state_names, current_snapshot):
    """현재 확률분포 스냅샷의 정확도를 측정한다."""
    names_and_labels = dict(map(lambda tup: (tup[0], find_max_val(tup[1])), current_snapshot))
    correct_nodes = []
    for node_name in state_names:
        if names_and_labels[node_name] == SOLUTION[node_name]:
            correct_nodes.append(node_name)
    return len(correct_nodes)


def calculate_stability(state_names, prev_snapshot, current_snapshot):
    """직전 확률분포 스냅샷에 대한 현재 확률분포 스냅샷의 stability를 측정한다.
       stability: time t에서의 stability: time (t-1)에서의 스냅샷과 비교했을 때 time t에서의 스냅샷에서 레이블이 달라진 노드의 개수."""
    names_and_labels_prev = dict(map(lambda tup: (tup[0], find_max_val(tup[1])), prev_snapshot))
    names_and_labels_current = dict(map(lambda tup: (tup[0], find_max_val(tup[1])), current_snapshot))
    changed_nodes = []
    for node_name in names_and_labels_current.keys():
        if names_and_labels_prev[node_name] != names_and_labels_current[node_name]:
            changed_nodes.append(node_name)
    return len(changed_nodes)


def calculate_precision_inferred(state_names, current_snapshot, number_of_interaction):
    """현재 확률분포 스냅샷을 보고, BN이 순수하게 infer한 것들 중에 맞힌 레이블의 개수를 구한다."""
    names_and_labels = dict(map(lambda tup: (tup[0], find_max_val(tup[1])), current_snapshot))
    correct_nodes = []
    for node_name in state_names:
        if names_and_labels[node_name] == SOLUTION[node_name]:
            correct_nodes.append(node_name)
    return len(correct_nodes) - number_of_interaction


def single_loop(snapshot_dict, graph_file, graph_for_reference,
                BN_for_inference, BN_for_inference_x, learned_evidence, **kwargs):
    """do a random or tactical loop on a given graph file
       - Available kwargs:
         - loop_type ([random|tactical]): whether we should use random/tactical loop for looping."""

    # the list of names of all states
    state_names = list(map(lambda node: node.name, BN_for_inference.states))

    # argument initialization
    initial_prediction_time = time.time()
    initial_raw_snapshot = BN_for_inference.predict_proba(learned_evidence, n_jobs=-1)
    initial_raw_snapshot_x = BN_for_inference.predict_proba(learned_evidence, n_jobs=-1)
    initial_snapshot = make_names_and_params(state_names, initial_raw_snapshot)
    initial_snapshot_x = make_names_and_params(state_names, initial_raw_snapshot_x)
    initial_precision_list = [np.nan for _ in range(len(BN_for_inference.states))]
    initial_stability_list = [np.nan for _ in range(len(BN_for_inference.states))]
    initial_precision_inferred_list = [np.nan for _ in range(len(BN_for_inference.states))]
    initial_window = [np.ndarray([0]) for _ in range(WINDOW_SIZE)]
    initial_asked = list(learned_evidence.keys())
    initial_evidence_x = {}
    initial_updated_nodes = []

    for initial_query in initial_asked:
        initial_updated_nodes += list(set(d_connected(graph_for_reference, BN_for_inference,
                                                      initial_query, initial_asked, state_names)))

    # random loop
    if kwargs["loop_type"] == "random":
        (final_snapshot, final_snapshot_x, precision_list, stability_list,
         precision_inferred_list, loop_time_list, final_asked, global_precisions) =\
             random_loop([], snapshot_dict, graph_for_reference, BN_for_inference, BN_for_inference_x,
                         0, initial_asked, learned_evidence, initial_evidence_x, initial_updated_nodes,
                         initial_snapshot, initial_snapshot_x, initial_precision_list, initial_stability_list,
                         initial_precision_inferred_list, [], initial_window, graph_file)

        draw_n_save(graph_file, BN_for_inference, precision_list, stability_list,
                    precision_inferred_list, loop_type='random')

    # tactical loop
    elif kwargs["loop_type"] == "tactical":
        (final_snapshot, final_snapshot_x, precision_list, stability_list,
         precision_inferred_list, loop_time_list, final_asked,
         final_evidence, global_precisions) =\
             tactical_loop([], snapshot_dict, graph_for_reference, BN_for_inference, BN_for_inference_x,
                           0, initial_asked, learned_evidence, initial_evidence_x, initial_updated_nodes,
                           initial_snapshot, initial_snapshot_x, initial_precision_list, initial_stability_list,
                           initial_precision_inferred_list, [], initial_window, graph_file)

        draw_n_save(graph_file, BN_for_inference, precision_list, stability_list,
                    precision_inferred_list, loop_type='tactical')

    return (loop_time_list, final_snapshot, final_snapshot_x,
            final_asked, global_precisions, final_evidence)


def one_pass(snapshot_dict, graph_file, graph_for_reference, BN_for_inference, BN_for_inference_x, lessons,
             prev_graph_states, prev_graph_file, debug=False):
    """하나의 그래프에 대해 BN을 굽고 interaction을 진행한다.
       Here, we don't need APIs instead of state_names, since we would like to
       transfer knowledge regarding EVERY methods, including user-defined ones."""
    state_names = list(map(lambda node: node.name, BN_for_inference.states))

    learned_evidence = transfer_knowledge.main(prev_graph_states, state_names, lessons)
    if debug:
        print("# of lessons:", len(lessons))
        print(graph_file, "has", len(state_names), "states")
        print("# of transferred evidence:", len(learned_evidence))
        if prev_graph_file is not None:
            # for debugging transfer
            with open(prev_graph_file + '->' + graph_file + '.txt', 'w+') as f:
                f.write(json.dumps(learned_evidence, indent=4))
        if lessons != {}:
            with open(prev_graph_file+"_lessons.txt", 'w+') as f:
                f.write(json.dumps(lessons, indent=4))

    print_num_of_APIS(BN_for_inference)

    (loop_time_list, final_snapshot, final_snapshot_x,
     final_asked, global_precisions, final_evidence) =\
        single_loop(snapshot_dict, graph_file, graph_for_reference,
                    BN_for_inference, BN_for_inference_x, learned_evidence, loop_type="tactical")

    lessons = transfer_knowledge.learn(lessons, final_snapshot, final_asked)  # update the lessons
    prev_graph_file = graph_file
    prev_graph_states = state_names

    return (lessons, final_snapshot_x, prev_graph_states,
            prev_graph_file, global_precisions, final_asked, final_evidence)


def evaluate_global_precision(snapshot_dict):
    num_of_correct_nodes = 0
    for _, snapshot in snapshot_dict.items():
        state_names = list(map(lambda tup: tup[0], snapshot))
        APIs = list(filter(lambda node: node in skip_funcs, state_names))
        num_of_correct_nodes += calculate_precision(APIs, snapshot)
    return (num_of_correct_nodes/len(skip_funcs)) * 100


# Checking BP results =====================================
# =========================================================


def check_snapshots_x(snapshot_dict_x, lessons, all_APIs):
    """Filter out spurious entries in snapshot_dict_x.
       (m, l) is a spurious entry <=> lessons[m] != l or
                                      very_similar(m, m') and lessons[m'] != l."""

    out = deepcopy(lessons)

    def very_similar(method1, method2):
        return VERY_SIMILAR[(VERY_SIMILAR["id1"] == method1) &
                            (VERY_SIMILAR["id2"] == method2)]

    def unanimous(dict_):
        if dict_ == dict():
            return True         # trivial case
        else:
            values = list(dict_.values())
            head = values[0]
            return reduce(lambda acc, elem: elem == head and acc, values, True)

    def take_a_vote(dict_):
        if dict_ == dict():
            return None
        else:
            all_values = set(dict_.values())
            all_values_dup = list(dict_.values())
            all_values_and_their_counts = list(map(lambda val: all_values_dup.count(val),
                                                   all_values_dup))
            return max(all_values_and_their_counts)

    def condition1(method, label):
        """condition 1: lessons[m] != l"""
        return lessons[method] != label

    def condition2(method, label):
        """condition 2: very_similar(m, m') and lessons[m'] != l"""
        very_similar_meths = []
        for other_method in all_APIs:
            if other_method == method:
                continue
            elif very_similar(method, other_method):
                very_similar_meths.append(other_method)
        very_similar_nodes_labels = dict(map(lambda meth: lessons[meth], very_similar_meths))
        if unanimous(very_similar_nodes_labels):
            some_entry = list(very_similar_nodes_labels.items())[0]  # 암거나 일단 골라봐
            unanimous_label = some_entry[1]
            return unanimous_label != label
        else:
            max_label = take_a_vote(very_similar_nodes_labels)
            return max_label != label

    for method, label in list(snapshot_dict_x.items()):
        if condition1(method, label) or condition1(method, label):
            del out[method]

    return out


def apply_to_final_snapshots(snapshot_dict_x, snapshot_dict,
                             final_evidence_dict, BN_dict):
    """1. Iterating through the snapshot_dict_x, do the following:
          1. take a snapshot_x of a graph
          2. add the snapshot_x's content to final_asked of that graph
          3. recompute the corresponding snapshot with the updated final_asked"""
    for graph_name, snapshot_x in list(snapshot_dict_x.items()):
        new_evidence = {**snapshot_x, **final_evidence_dict[graph_name]}
        my_BN = BN_dict[graph_name]
        print("new_evidence", new_evidence)
        new_raw_snapshot = my_BN.predict_proba(new_evidence, n_jobs=-1)
        my_state_names = list(map(lambda node: node.name, my_BN.states))
        new_snapshot = make_names_and_params(my_state_names, new_raw_snapshot)

        # now, update the snapshot_dict
        snapshot_dict[graph_name] = new_snapshot

    return snapshot_dict


# Main ====================================================
# =========================================================


def main():
    graph_files = [f for f in os.listdir('.') if re.match(r'.*_graph_[0-9]+$', f)]
    graph_files = list(filter(lambda x: '_poor' not in x, graph_files))
    lessons = {}
    prev_graph_states = None
    prev_graph_file = None
    BN_queue = []
    snapshot_dict = {}
    snapshot_dict_x = {}
    final_evidence_dict = {}
    global_precision_list = []
    all_state_names = []
    BN_dict = {}

    print("Baking BNs...", end="")

    for graph_file in graph_files:
        graph_for_reference = nx.read_gpickle(graph_file)
        graph_for_reference.name = graph_file
        BN_for_inference = make_BN.main(graph_for_reference)
        BN_for_inference_x = make_BN.main(graph_for_reference)
        if len(BN_for_inference.states) == 0:
            continue
        state_names = list(map(lambda node: node.name, BN_for_inference.states))
        all_state_names += state_names
        initial_raw_snapshot = BN_for_inference.predict_proba({}, n_jobs=-1)
        initial_snapshot = make_names_and_params(state_names, initial_raw_snapshot)
        snapshot_dict[graph_file] = initial_snapshot
        BN_for_inference.name = graph_file
        BN_dict[graph_file] = BN_for_inference
        BN_queue.append((graph_for_reference, BN_for_inference, BN_for_inference_x))

    print("done")

    all_APIs = list(filter(lambda method: method in skip_func, all_state_names))

    # evaluate the initial global precision of snapshot_dict and add it to global_precision_list
    global_precision_list.append(evaluate_global_precision(snapshot_dict))

    for graph, BN, BN_x in BN_queue:
        (lessons, final_snapshot_x, prev_graph_states,
         prev_graph_file, global_precisions, final_asked, final_evidence) =\
            one_pass(snapshot_dict, graph.name, graph, BN, BN_x, lessons,
                     prev_graph_states, prev_graph_file, debug=True)
        snapshot_dict_x[graph_file] = final_snapshot_x
        final_evidence_dict[graph_file] = final_evidence
        global_precision_list += global_precisions

    # The blank spaces
    for _ in range(len(skip_funcs)-len(global_precision_list)):
        global_precision_list.append(np.nan)

    print("Now inspecting BP results and applying...", end="")
    filtered_snapshots_x = check_snapshots_x(snapshot_dict_x, lessons, all_APIs)
    snapshot_dict_applied = apply_to_final_snapshot(filtered_snapshots_x, snapshot_dict,
                                                    final_evidence_dict, BN_dict)
    print("done")

    print("Now draw-n-saving global precision graph...", end="")
    draw_n_save_global_precision_graph(global_precision_list)
    print("done")

    print("Now saving inferrence results...", end="")
    # TODO
    print("done")


if __name__ == "__main__":
    main()
