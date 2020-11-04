from pomegranate import *
import time
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as ptch
import matplotlib.axes as axes
import csv
import networkx as nx
import itertools as it
import os
import os.path
import random
import make_BN
import json

from datetime import datetime
from solutions import *
from scrape_oracle_docs import *
from toolz import valmap
from matplotlib.ticker import MaxNLocator
from create_node import process
from make_underlying_graph import find_edge_labels
from make_CPT import *

import modin.pandas as pd

# Constants ========================================
# ==================================================

NOW = datetime.now().strftime("%Y-%m-%d-%H:%M:%S")
GRAPH_FILE_NAME = "graph_for_reference"
graph_for_reference = nx.read_gpickle(GRAPH_FILE_NAME)
BN_for_inference = make_BN.main(GRAPH_FILE_NAME)

df_data = open("df.csv", "r+")
df_reader = csv.reader(df_data)

call_data = open("callg.csv", "r+")
call_reader = csv.reader(call_data)

DF_EDGES = list(df_reader)
CALL_EDGES = list(call_reader)
STATE_NAMES = list(map(lambda node: node.name, BN_for_inference.states))


def there_may_be_solution():
    with open("paths.json", "r+") as pathjson:
        SOLUTION_PATH = json.load(pathjson)["solution_directory"]
    try:
        with open(SOLUTION_PATH, "r+") as solutionjson:
            return json.load(solutionjson)
    except:
        return None


SOLUTION = there_may_be_solution()


# Exceptions ========================================
# ===================================================

class ThisIsImpossible(Exception):
    pass

# random loop ============================================
# ========================================================

def random_loop(BN_for_inference, graph_for_reference, interaction_number,
                current_asked, current_evidence, prev_snapshot,
                precision_list, stability_list, precision_inferred_list,
                inference_time_list, **kwargs):
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
            - inference_time_list: accumulated times took in belief propagation
       Available kwargs: have_solution [True|False]: Do you have the complete solution for the benchmark?"""

    random_index = random.randint(0, len(BN_for_inference.states)-1)
    query = state_names[random_index]
    while query in current_asked:
        random_index = random.randint(0, len(BN_for_inference.states)-1)
        query = STATE_NAMES[random_index].name

    its_time_to_terminate = time_to_terminate(BN_for_inference, current_evidence)

    # exit the function based on confidence.
    if its_time_to_terminate:
        if kwargs["have_solution"]:
            draw_precision_graph(list(range(1, len(BN_for_inference.states)+1)),
                                 precision_list, interactive=False, loop_type="random")
            draw_stability_graph(list(range(1, len(BN_for_inference.states)+1)),
                                 stability_list, interactive=False, loop_type="random")
            draw_precision_inferred_graph(list(range(1, len(BN_for_inference.states)+1)),
                                          stability_list, interactive=False, loop_type="random")
        return prev_snapshot, precision_list, stability_list, precision_inferred_list

    oracle_response = input("What label does <" + query + "> bear? [src|sin|san|non]: ")

    if oracle_response == 'src':
        current_evidence[query] = 1
    elif oracle_response == 'sin':
        current_evidence[query] = 2
    elif oracle_response == 'san':
        current_evidence[query] = 3
    elif oracle_response == 'non':
        current_evidence[query] = 4
    elif oracle_response == 'exit':
        if kwargs["have_solution"]:
            draw_precision_graph(list(range(1, len(BN_for_inference.states)+1)),
                                 precision_list, interactive=False, loop_type="random")
            draw_stability_graph(list(range(1, len(BN_for_inference.states)+1)),
                                 stability_list, interactive=False, loop_type="random")
            draw_precision_inferred_graph(list(range(1, len(BN_for_inference.states)+1)),
                                          stability_list, interactive=False, loop_type="random")
        return prev_snapshot, precision_list, stability_list, precision_inferred_list

    current_asked.append(query)

    # the new snapshot after the observation and its inference time
    inference_start = time.time()
    new_snapshot = BN_for_inference.predict_proba(current_evidence, n_jobs=-1)
    current_inference_time = time.time()-inference_start
    inference_time_list.append(current_inference_time)

    if kwargs["have_solution"]:
        # the new precision after the observation
        current_precision = calculate_precision(new_snapshot)
        precision_list[interaction_number] = current_precision

        # the new stability after the observation
        current_stability = calculate_stability(prev_snapshot, new_snapshot)
        stability_list[interaction_number] = current_stability

        # the new precision purely inferred by the BN, after the observation
        current_precision_inferred = calculate_precision_inferred(new_snapshot, interaction_number)
        precision_inferred_list[interaction_number] = current_precision_inferred

    # print the number of confident nodes
    print("# of confident nodes: ", count_confident_nodes(new_snapshot))

    # visualize the current status if necessary
    if kwargs["have_solution"]:
        visualize_snapshot(new_snapshot, [])
        draw_precision_graph(list(range(1, len(BN_for_inference.states)+1)),
                             precision_list, interactive=True, loop_type="random")
        draw_stability_graph(list(range(1, len(BN_for_inference.states)+1)),
                             stability_list, interactive=True, loop_type="random")
        draw_precision_inferred_graph(list(range(1, len(BN_for_inference.states)+1)),
                                      stability_listinteractive=True, loop_type="random")

    # loop!
    return random_loop(BN_for_inference, graph_for_reference, interaction_number+1,
                       current_asked, current_evidence, new_snapshot,
                       precision_list, stability_list, precision_inferred_list, inference_time_list, **kwargs)
    
# tactical loop and its calculations ====================
# ========================================================

def tactical_loop(graph_for_reference, interaction_number,
                  current_asked, current_evidence, updated_nodes,
                  prev_snapshot, precision_list, stability_list,
                  precision_inferred_list, inference_time_list, **kwargs):
    """The main interaction functionality (loops via recursion), asking tactically using d-separation
       Parameters:
            - graph_for_reference: the underlying graph.
            - interaction_number: number of interactions performed so far.
            - current_asked: names of currently asked nodes.
            - current_evidence: dict of given evidences accumulated so far
            - updated_nodes: updated nodes which are currently being tracked of
            - prev_snapshot: snapshot from the previous call
            - precision_list: accumulated precision values
            - stability_list: accumulated stability values
            - precision_inferred_list: accumulated precision values purely inferred by the BN
            - inference_time_list: accumulated times took in belief propagation
       Available kwargs: have_solution [True|False]: Do you have the complete solution for the benchmark?"""

    loop_start = time.time()

    # some variables to make our code resemble English
    there_are_nodes_left = find_max_d_con(current_asked, updated_nodes, STATE_NAMES)
    there_are_no_nodes_left = not there_are_nodes_left
    its_time_to_terminate = time_to_terminate(BN_for_inference, current_evidence)
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
        if set(STATE_NAMES) == set(current_asked):
            print("\nWarning: some distributions are not fully determined.\n")
            if kwargs["have_solution"]:
                draw_precision_graph(list(range(1, len(BN_for_inference.states)+1)),
                                     precision_list, interactive=False, loop_type="tactical")
                draw_stability_graph(list(range(1, len(BN_for_inference.states)+1)),
                                     stability_list, interactive=False, loop_type="tactical")
                draw_precision_inferred_graph(list(range(1, len(BN_for_inference.states)+1)),
                                              stability_list, interactive=False, loop_type="tactical")
            return prev_snapshot, precision_list, stability_list, precision_inferred_list
        else:
            query, dependent_nodes = find_max_d_con([], [], remove_sublist(STATE_NAMES, current_asked))
    elif there_are_no_nodes_left and its_time_to_terminate:
        if kwargs["have_solution"]:
            draw_precision_graph(list(range(1, len(BN_for_inference.states)+1)),
                                 precision_list, interactive=False, loop_type="tactical")
            draw_stability_graph(list(range(1, len(BN_for_inference.states)+1)),
                                 stability_list, interactive=False, loop_type="tactical")
            draw_precision_inferred_graph(list(range(1, len(BN_for_inference.states)+1)),
                                          stability_list, interactive=False, loop_type="tactical")
        return prev_snapshot, precision_list, stability_list, precision_inferred_list
    elif there_are_nodes_left and not_yet_time_to_terminate:
        pass
    elif there_are_nodes_left and its_time_to_terminate:
        return prev_snapshot, precision_list, stability_list, precision_inferred_list

    # ask the chosen method and fetch the answer from the solutions
    oracle_response = input("What label does <" + query + "> bear? [src|sin|san|non]: ")
    updated_nodes += list(d_connected(query, current_asked, STATE_NAMES))

    if oracle_response == 'src':
        current_evidence[query] = 1
    elif oracle_response == 'sin':
        current_evidence[query] = 2
    elif oracle_response == 'san':
        current_evidence[query] = 3
    elif oracle_response == 'non':
        current_evidence[query] = 4
    elif oracle_response == 'exit':
        if kwargs["have_solution"]:
            draw_precision_graph(list(range(1, len(BN_for_inference.states)+1)),
                                 precision_list, interactive=False, loop_type="tactical")
            draw_stability_graph(list(range(1, len(BN_for_inference.states)+1)),
                                 stability_list, interactive=False, loop_type="tactical")
            draw_precision_inferred_graph(list(range(1, len(BN_for_inference.states)+1)),
                                          stability_list, interactive=False, loop_type="tactical")
        return prev_snapshot, precision_list, stability_list, precision_inferred_list

    current_asked.append(query)

    # the new snapshot after the observation and its inference time
    inference_start = time.time()
    new_snapshot = BN_for_inference.predict_proba(current_evidence, n_jobs=-1)
    current_inference_time = time.time()-inference_start
    inference_time_list.append(current_inference_time)

    if kwargs["have_solution"]:
        # the new precision after the observation
        current_precision = calculate_precision(new_snapshot)
        precision_list[interaction_number] = current_precision
        
        # the new stability after the observation
        current_stability = calculate_stability(prev_snapshot, new_snapshot)
        stability_list[interaction_number] = current_stability
        
        # the new precision purely inferred by the BN, after the observation
        current_precision_inferred = calculate_precision_inferred(new_snapshot, interaction_number)
        precision_inferred_list[interaction_number] = current_precision_inferred
        
    # print the number of confident nodes
    print("# of confident nodes: ", count_confident_nodes(new_snapshot))

    # visualize the current status if necessary
    if kwargs["have_solution"]:
        visualize_snapshot(new_snapshot, [])
        draw_precision_graph(list(range(1, len(BN_for_inference.states)+1)),
                             precision_list, interactive=True, loop_type="tactical")
        draw_stability_graph(list(range(1, len(BN_for_inference.states)+1)),
                             stability_list, interactive=True, loop_type="tactical")
        draw_precision_inferred_graph(list(range(1, len(BN_for_inference.states)+1)),
                                      stability_list, interactive=True, loop_type="tactical")

    # loop!
    return tactical_loop(graph_for_reference, interaction_number+1,
                         current_asked, current_evidence, updated_nodes,
                         new_snapshot, precision_list, stability_list,
                         precision_inferred_list, inference_time_list, **kwargs)


def d_connected(node, current_asked, pool):
    """현재까지 물어본 노드들이 주어졌을 때, node와 조건부 독립인 노드들의 set을 찾아낸다. Complexity: O(n)."""
    out = set()
    for other_node in STATE_NAMES:
        if nx.d_separated(graph_for_reference, {node}, {other_node}, set(current_asked)):
            out.add(other_node)
    return set(STATE_NAMES) - out


def remove_sublist(lst, sublst):
    """remove the sublst from lst without any side-effect."""
    out = []
    for elem in lst:
        if elem not in sublst:
            out.append(elem)
    return out


def forall(unary_pred, collection):
    return reduce(lambda acc, elem: unary_pred(elem) and acc, collection, True)


def find_max_d_con(current_asked, updated_nodes, list_of_all_nodes):
    node_dataframe = pd.DataFrame(list_of_all_nodes, columns=['nodes'])
    mapfunc = lambda row: len(d_connected(row['nodes'], current_asked,
                                          list_of_all_nodes)-set(current_asked)-set(updated_nodes))
    d_con_set_len = node_dataframe.apply(mapfunc, axis=1)
    if d_con_set_len.mask(d_con_set_len == 0).dropna().empty:
        return None
    node_dataframe["d_con_set_len"] = d_con_set_len
    node_dataframe.sort_values(by=["d_con_set_len"], inplace=True, ascending=False)
    return node_dataframe.iloc[0].nodes, node_dataframe.iloc[0].d_con_set_len


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


def count_confident_nodes(snapshot):
    # the distribution across random variables' values
    names_and_params = make_names_and_params(snapshot)
    params = list(map(lambda tup: tup[1], names_and_params))
    # list of lists of the probabilities across random variables' values, extracted from dist_dicts
    dist_probs = list(map(lambda dist: list(dist.values()), params))
    # Do all the nodes' probability lists satisfy is_confident()?
    acc = 0
    for lst in dist_probs:
        if is_confident(lst):
            acc += 1
    return acc


def time_to_terminate(BN, current_evidence):
    # the distribution across random variables' values
    names_and_params = make_names_and_params(BN_for_inference.predict_proba(current_evidence, n_jobs=-1))
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

def visualize_snapshot(snapshot, dependent_nodes):
    """한번 iteration 돌 때마다, 전체 BN의 snapshot을 가시화한다. 이 때, confident node들 위에는 `conf`라는 문구를 띄운다."""
    network_figure = plt.figure("Bayesian Network", figsize=(30, 15))
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
    # coord_lists = []
    # for dependent_node in dependent_nodes:
    #     coord_lists.append(node_posmap[dependent_node])
    # coord_lists = np.asarray(coord_lists)
    # polygon = ptch.Polygon(coord_lists, closed=True, alpha=0.4)
    # ax.add_patch(polygon)

    # graph_for_reference의 G에서 lost node를 차집합
    acc = set()
    for node_name in list(graph_for_reference.nodes):
        if node_name not in STATE_NAMES:
            graph_for_reference.remove_node(node_name)

    nx.draw(graph_for_reference,
            node_color=node_colormap, edge_color=edge_colormap,
            pos=node_posmap,
            ax=ax,
            with_labels=True, node_size=100, font_size=8)

    plt.show()


def draw_precision_graph(x, y, **kwargs):
    """precision graph를 그리는 함수. NOTE: x와 y의 input 길이를 맞춰줘야 함.
       Available kwargs:
           - interactive [True|False]: Interactively show & update vs. save as png file"""

    plt.ion()
    precision_figure = plt.figure("Precision")
    ax = precision_figure.gca()
    ax.xaxis.set_major_locator(MaxNLocator(integer=True))
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    precision_figure.clf()
    num_of_states = len(STATE_NAMES)
    plt.xlim(1, num_of_states)
    plt.ylim(0, num_of_states)
    plt.xlabel('# of interactions')
    plt.ylabel('# of correct nodes')
    plt.title("Precision development during interaction")
    plt.plot(x, y, 'b-')

    if kwargs["interactive"]:
        precision_figure.canvas.draw()
    else:
        if not os.path.isdir(GRAPH_FILE_NAME+"_stats"):
            os.mkdir(GRAPH_FILE_NAME+"_stats")
        plt.savefig(GRAPH_FILE_NAME+"_stats"+os.sep+\
                    "precision_graph_"+NOW+"_"+kwargs["loop_type"]+".png")
    

def draw_stability_graph(x, y, **kwargs):
    """stability graph를 그리는 함수. NOTE: x와 y의 input 길이를 맞춰줘야 함.
       Available kwargs:
           - interactive [True|False]: Interactively show & update vs. save as png file"""

    plt.ion()
    stability_figure = plt.figure("Stability")
    ax = stability_figure.gca()
    ax.xaxis.set_major_locator(MaxNLocator(integer=True))
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    stability_figure.clf()
    num_of_states = len(STATE_NAMES)
    plt.xlim(1, num_of_states)
    plt.ylim(0, num_of_states)
    plt.xlabel("# of interactions")
    plt.ylabel('# of changed nodes')
    plt.title("Stability development during interaction")
    plt.plot(x, y, 'b-')
    
    if kwargs["interactive"]:
        stability_figure.canvas.draw()
    else:
        if not os.path.isdir(GRAPH_FILE_NAME+"_stats"):
            os.mkdir(GRAPH_FILE_NAME+"_stats")
        plt.savefig(GRAPH_FILE_NAME+"_stats"+os.sep+\
                    "stability__graph_"+NOW+"_"+kwargs["loop_type"]+".png")


def draw_precision_inferred_graph(x, y, **kwargs):
    """stability graph를 그리는 함수. NOTE: x와 y의 input 길이를 맞춰줘야 함.
       Available kwargs:
           - interactive [True|False]: Interactively show & update vs. save as png file"""

    plt.ion()
    precision_inferred_figure = plt.figure("Inferred Precision")
    ax = precision_inferred_figure.gca()
    ax.xaxis.set_major_locator(MaxNLocator(integer=True))
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    precision_inferred_figure.clf()
    num_of_states = len(STATE_NAMES)
    plt.xlim(1, num_of_states)
    plt.ylim(0, num_of_states)
    plt.xlabel("# of interactions")
    plt.ylabel('# of correctly inferred nodes')
    plt.title("Inferred precision development during interaction")
    plt.plot(x, y, 'b-')
    
    if kwargs["interactive"]:
        precision_inferred_figure.canvas.draw()
    else:
        if not os.path.isdir(GRAPH_FILE_NAME+"_stats"):
            os.mkdir(GRAPH_FILE_NAME+"_stats")
        plt.savefig(GRAPH_FILE_NAME+"_stats"+os.sep+\
                    "precision_inferred_graph_"+NOW+"_"+kwargs["loop_type"]+".png")
        
        

def create_node_colormap(names_and_labels):
    """BN을 기준으로 계산된 names_and_labels를 받아서 graph_for_reference를 기준으로 한 colormap을 만든다."""
    out = list(STATE_NAMES)[:]
    for name, label in names_and_labels:
        index = out.index(name)
        out[index] = node_colordict[label]
    return out


def create_edge_colormap():
    """엣지 목록을 받아서, 엣지의 종류에 따라 graph_for_reference를 그릴 때 엣지의 색깔을 달리한다."""
    out = list(graph_for_reference.edges)[:]
    for edge in out:
        index = out.index(edge)
        if edge in DF_EDGES:      # df
            out[index] = "red"
        elif edge in CALL_EDGES:  # call
            out[index] = "green"
        else:                     # sim
            out[index] = "blue"
    return out


def make_names_and_params(snapshot):
    """snapshot을 읽어서, 랜덤변수 별 확률값의 dict인 parameters만을 빼낸 다음 node의 이름과 짝지어서 list에 담아 낸다."""
    dists = []
    node_name_list = list(STATE_NAMES)
    for dist in snapshot:
        if type(dist) == int:  # oracle에 의해 고정된 경우!
            dists.append(normalize_dist(dist))
        else:
            dists.append(dist.parameters[0])
    names_and_params = list(zip(node_name_list, dists))
    return names_and_params


def report_results(initial_snapshot, final_snapshot):
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
    nodes = list(STATE_NAMES)
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
    for node_name in STATE_NAMES:
        if names_and_labels[node_name] == SOLUTION[node_name]:
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
    for node_name in names_and_labels_current.keys():
        if names_and_labels_prev[node_name] != names_and_labels_current[node_name]:
            changed_nodes.append(node_name)
    return len(changed_nodes)


def calculate_precision_inferred(current_snapshot, number_of_interaction):
    """현재 확률분포 스냅샷을 보고, BN이 순수하게 infer한 것들 중에 맞힌 레이블의 개수를 구한다."""
    # current_snapshot의 타입은? np.array of Distribution.
    names_and_params = make_names_and_params(current_snapshot)
    names_and_labels = dict(map(lambda tup: (tup[0], find_max_val(tup[1])), names_and_params))
    correct_nodes = []
    for node_name in STATE_NAMES:
        if names_and_labels[node_name] == SOLUTION[node_name]:
            correct_nodes.append(node_name)
    return len(correct_nodes) - number_of_interaction


# main ====================================================
# =========================================================

def main():
    initial_prediction_time = time.time()
    initial_snapshot = BN_for_inference.predict_proba({}, n_jobs=-1)
    print("initial predicition_time:", time.time() - initial_prediction_time)
    number_of_states = len(BN_for_inference.states)
    initial_precision_list = [np.nan for _ in range(len(BN_for_inference.states))]
    initial_stability_list = [np.nan for _ in range(len(BN_for_inference.states))]
    initial_precision_inferred_list = [np.nan for _ in range(len(BN_for_inference.states))]
    print()  # for aesthetics in the REPL

    # random loop
    # print("\nEntering random loop.\nPress 'exit' on the prompt to exit the loop.\n")
    # final_snapshot, precision_list, stability_list, precision_inferred_list =\
    #     random_loop(BN_for_inference, graph_for_reference, 0,
    #                 list(), dict(), initial_snapshot,
    #                 initial_precision_list, initial_stability_list,
    #                 initial_precision_inferred_list, list(), have_solution=True)

    # tactical loop
    print("\nEntering tactical loop.\nPress 'exit' on the prompt to exit the loop.\n")
    final_snapshot, precision_list, stability_list, precision_inferred_list=\
        tactical_loop(graph_for_reference, 0,
                      list(), dict(), list(),
                      initial_snapshot, initial_precision_list, initial_stability_list,
                      initial_precision_inferred_list, list(), have_solution=False)

    print("Inference done.")

    # save the data
    save_data_as_csv(final_snapshot)
    print("Data saved as inferred.csv")


if __name__ == "__main__":
    main()
