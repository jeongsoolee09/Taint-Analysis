# 백지 상태에서 시작하지 않고, 이전 경험에서부터 배우도록 하자.
import networkx as nx
import pandas as pd
import extra_features
import re
import json

import pickle

from operator import itemgetter
from split_underlying_graph import draw_callgraph
from create_edge import no_symmetric
from create_node import process
from itertools import product, repeat
from pomegranate import *

# Constants ============================================
# ======================================================

SIMS = pd.read_csv("pairwise_sims.csv", index_col=0)
CALLGRAPH = nx.read_gpickle("callgraph")
EXTRA_FEATURES_PREV = None      # extra features for previous graph
EXTRA_FEATURES_NEXT = None      # extra features for next graph


def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]

PROJECT_ROOT_DIR = retrieve_path()

with open(PROJECT_ROOT_DIR+"skip_func.txt", "r+") as skip_func:
    SKIP_FUNCS = skip_func.readlines()
    SKIP_FUNCS = list(map(lambda string: string.rstrip(), SKIP_FUNCS))


# Functions ============================================
# ======================================================

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


# https://stackoverflow.com/questions/29916065/how-to-do-camelcase-split-in-python
def camel_case_split(identifier):
    matches = re.finditer('.+?(?:(?<=[a-z])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])|$)', identifier)
    return [m.group(0) for m in matches]


def find_oracle_response(final_snapshot, current_asked):
    oracle_responses = []
    target_params = [{1.0: 1, 2.0: 0, 3.0: 0, 4.0: 0},
                     {1.0: 0, 2.0: 1, 3.0: 0, 4.0: 0},
                     {1.0: 0, 2.0: 0, 3.0: 1, 4.0: 0},
                     {1.0: 0, 2.0: 0, 3.0: 0, 4.0: 1}]
    for state_name, param in final_snapshot:
        if param in target_params:
            label, _ = max(param.items(), key=itemgetter(1))
            oracle_responses.append((state_name, label))
    return oracle_responses


def find_conf_sols(final_snapshot, current_asked):
    conf_sols = []
    target_params = [{1.0: 1, 2.0: 0, 3.0: 0, 4.0: 0},
                     {1.0: 0, 2.0: 1, 3.0: 0, 4.0: 0},
                     {1.0: 0, 2.0: 0, 3.0: 1, 4.0: 0},
                     {1.0: 0, 2.0: 0, 3.0: 0, 4.0: 1}]
    for state_name, param in final_snapshot:
        if param not in target_params and is_confident(param):
            label, _ = max(param.items(), key=itemgetter(1))
            conf_sols.append((state_name, label))
    return conf_sols

# A lesson is a dict from a node to label(1.0, 2.0, 3.0, 4.0).


def learn(previous_lessons, final_snapshot, current_asked):
    """이전의 lesson들과 confident 노드들, 그리고 oracle response를 모두 모아 내놓는다."""
    oracle_response = dict(find_oracle_response(final_snapshot, current_asked))
    # conf_sols = dict(find_conf_sols(final_snapshot, current_asked))
    # previous_lessons_nodes = {**oracle_response, **conf_sols}
    # return {**previous_lessons, **previous_lessons_nodes}
    return {**previous_lessons, **oracle_response}


def convert_bool_to_int(df):
    df = df.replace(['True'], [1])
    df = df.replace([True], [1])
    df = df.replace(['False'], [0])
    df = df.replace([False], [0])
    return df


# Tentative rule activator ===================================
# ============================================================


def activate_getter_setter(lessons):
    """previous_lessons_nodes에 getter/setter가 포함되어 있는지, 확인"""
    for node, label in lessons.items():
        row = EXTRA_FEATURES_PREV[EXTRA_FEATURES_PREV['name']==node]
        if row.empty:
            continue
        if row["getter_setter"].item() == "getter" or\
           row["getter_setter"].item() == "setter":
            if label == 4.0:
                return True         # 거봐 내 말이 맞다니까
        else:
            continue                # 두고 봐 진짜라니까


def activate_hashCode_is_san(lessons):
    """lessons에 hashCode가 포함되어 있는지를 확인"""
    for node, label in lessons.items():
        row = EXTRA_FEATURES_PREV[EXTRA_FEATURES_PREV['name']==node]
        if row.empty:
            continue
        if row["is_hashCode"].item():
            if label == 3.0:
                return True     # 거봐 내 말이 맞다니까
        else:
            continue            # 두고 봐 진짜라니까


def activate_assert_is_san(lessons):
    """lessons에 assert*가 포함되어 있는지를 확인"""
    for node, label in lessons.items():
        row = EXTRA_FEATURES_PREV[EXTRA_FEATURES_PREV['name']==node]
        if row.empty:
            continue
        if row["is_assert"].item():
            if label == 3.0:
                return True     # 거봐 내 말이 맞다니까
        else:
            continue            # 두고 봐 진짜라니까


def activate_to_is_non(lessons):
    """# lessons에 is*가 포함되어 있는지를 확인"""
    for node, label in lessons.items():
        row = EXTRA_FEATURES_PREV[EXTRA_FEATURES_PREV['name']==node]
        if row.empty:
            continue
        if row["is_to"].item():
            if label == 4.0:
                return True
        else:
            continue


def activate_wrapping_primitives_is_non(lessons):
    """lessons에 primitive 타입을 wrapping하는 클래스 메소드가 포함되어 있는지를 확인"""
    for node, label in lessons.items():
        row = EXTRA_FEATURES_PREV[EXTRA_FEATURES_PREV['name']==node]
        if row.empty:
            continue
        if row["is_wrapping_primitive"].item():
            if label == 4.0:
                return True
        else:
            continue


def activate_builtin_collection_is_non(lessons):
    """lessons에 builtin collection 클래스 메소드가 포함되어 있는지를 확인"""
    for node, label in lessons.items():
        row = EXTRA_FEATURES_PREV[EXTRA_FEATURES_PREV['name']==node]
        if row.empty:
            continue
        if row["is_builtin_coll"].item():
            if label == 4.0:
                return True
        else:
            continue


def activate_GET_POST_SELECT(lessons):
    """lessons에 [GET|POST|SELECT] annotation을 달고 있는 메소드가 있는지 확인"""
    for node, label in lessons.items():
        row = EXTRA_FEATURES_PREV[EXTRA_FEATURES_PREV['name']==node]
        if row.empty:
            continue
        if row["is_GET_POST_SELECT"].item() == "GET":
            if label == 2.0:
                return True
        elif row["is_GET_POST_SELECT"].item() == "POST":
            if label == 1.0:
                return True
        elif row["is_GET_POST_SELECT"].item() == "SELECT":
            if label == 2.0:
                return True
        else:
            continue


# Tentative rules ============================================
# ============================================================

# A "tentative rule" is an [activated|non-activated] function from pd.DataFrame * Methnames -> dict().
# A tentative rule gets activated only if the corresponding activator returns True

def getter_setter_is_non(**kwargs):
    """다음에 사용될 노드들 중에서 getter와 setter에 대해 미리 문답을 해 놓는다."""
    if kwargs["activated"]:
        learned = dict()
        for row in EXTRA_FEATURES_NEXT.itertuples():
            method_name = row[1]
            if row[2] == "getter" or row[2] == "setter":
                learned[method_name] = 4.0
        return learned
    else:
        return dict()


def hashCode_is_san(**kwargs):
    """다음에 사용될 노드들 중에서 hashCode들에 대해 미리 문답을 해 놓는다."""
    if kwargs["activated"]:
        learned = dict()
        for row in EXTRA_FEATURES_NEXT.itertuples():
            method_name = row[1]
            if method_name == "hashCode":
                learned[method_name] = 3.0
        return learned
    else:
        return dict()


def assert_is_san(**kwargs):
    """다음에 사용될 노드들 중에서 is로 시작하는 메소드들에 대해 미리 문답을 해 놓는다."""
    if kwargs["activated"]:
        learned = dict()
        for row in EXTRA_FEATURES_NEXT.itertuples():
            method_name = row[1]
            if "assert" in method_name:
                learned[method_name] = 3.0
        return learned
    else:
        return dict()


def to_is_non(**kwargs):
    """다음에 사용될 노드들 중에서 to로 시작하는 메소드들에 대해 미리 문답을 해 놓는다."""
    if kwargs["activated"]:
        learned = dict()
        for row in EXTRA_FEATURES_NEXT.itertuples():
            method_name = row[1]
            if "is" == camel_case_split(method_name)[0]:
                learned[method_name] = 4.0
        return learned
    else:
        return dict()


def wrapping_primitives_is_non(**kwargs):
    """다음에 사용될 노드들 중에서 primitive를 wrapping하는 메소드들에 대해 미리 문답을 해 놓는다."""
    if kwargs["activated"]:
        learned = dict()
        for row in EXTRA_FEATURES_NEXT.itertuples():
            method_name = row[1]
            if row[6]:
                learned[method_name] = 4.0
        return learned
    else:
        return dict()


def builtin_collection_is_non(**kwargs):
    """다음에 사용될 노드들 중에서 builtin collection class의 메소드들에 대해 미리 문답을 해 놓는다."""
    if kwargs["activated"]:
        learned = dict()
        for row in EXTRA_FEATURES_NEXT.itertuples():
            method_name = row[1]
            if row[7]:
                learned[method_name] = 4.0
        return learned
    else:
        return dict()


def GET_POST_SELECT_is_sin_or_src(**kwargs):
    if kwargs["activated"]:
        learned = dict()
        for row in EXTRA_FEATURES_NEXT.itertuples():
            method_name = row[1]
            if row[8] == "GET":
                learned[method_name] = 2.0
            elif row[8] == "POST":
                learned[method_name] = 1.0
            elif row[8] == "SELECT":
                learned[method_name] = 2.0
        return learned
    else:
        return dict()


# evidence builders ==========================================
# ============================================================


def pairwise_similarity(lessons, state_names):
    """lessons의 내용을 보고, state_names 중에서 충분히 닮은 것들을 찾아낸다.
       lessons: node name |-> label의 dictionary
       state_names: string list, 그 다음에 interaction할 그래프의 모든 state들 (API, non-API 포함)"""

    # There are no lessons accumulated when the loop first starts
    if lessons == dict():
        return dict()

    # Prepare two DataFrames
    lesson_df = pd.DataFrame(lessons.items(), columns=["id1", "lessons_labels"])
    state_names_df = pd.DataFrame(state_names, columns=["id2"])

    # find the similar enough ones:
    # either find: (previous_lessons_node, state_name) or
    #              (state_name, previous_lessons_node) in SIMS dataframe
    # To do so, we create a Cartesian Product of previous_lessons_nodes and state_names,
    # and check for each row if it exists in the SIMS dataframe.

    # Warning: SQL Magic ahead!

    # The Cartesian Product.
    carpro = lesson_df.merge(state_names_df, how="cross")

    # perform a left-join
    left_join = pd.merge(carpro, SIMS, on=["id1", "id2"], how="left", indicator="exists?")

    # only select "id1", "id2", and "exists?"
    projected = left_join.filter(["id1", "id2", "lessons_labels", "exists?"])

    # only select the rows which exists in both SIMS and carpro
    selected = projected[projected["exists?"] == "both"]

    # drop the column from sample_lesson_df
    selected = selected.drop(columns=["id1"])

    raw_dict = selected.to_dict('records')

    return dict(map(lambda dict_: tuple(dict_.values())[0:2], raw_dict))


def row_isin_dataframe(node1, node2):
    return not SIMS[(SIMS["id1"] == node1) &
                    (SIMS["id2"] == node2)].empty


def one_call_relation(lessons, state_names):
    """lessons의 내용을 보고, state_names 중에서 1-call 관계에 있는 노드들을 찾아낸다."""
    # 맨 처음 loop을 돌 때는 lesson이 안 쌓여 있기 때문
    if lessons == dict():
        return dict()

    # 충분히 similar한 것들 찾아내기

    # 전처리: (class, rtntype, methodname, intype, id)의 튜플 리스트로 만들기
    previous_lessons_nodes = list(lessons.keys())
    previous_lessons_nodes = list(map(process, previous_lessons_nodes))

    state_names = list(map(process, state_names))
    one_call_nodes = []
    for edge1, edge2 in list(CALLGRAPH.edges):
        if edge2 in previous_lessons_nodes:
            label = lessons[edge2]
            if edge1 in state_names:
                one_call_nodes.append((edge1, label))

    one_call_nodes = dict(one_call_nodes)

    return one_call_nodes


def a_priori_rules(lessons, state_names, # 여기서 state_names는 그 다음에 물어볼 그래프의 노드들의 이름들.
                   EXTRA_FEATURE_PREV,
                   EXTRA_FEATURE_NEXT):
    """굳이 물어보지 않아도 아는 것들: activate된 tentative rule들을 바탕으로, 해당되는 노드들을 찾아낸다."""
    # tentative rule들을 사용한다.
    # getter_setter_dict = getter_setter_is_non(activated=activate_getter_setter(lessons))

    # hashCode_dict = hashCode_is_san(activated=activate_hashCode_is_san(lessons))

    # assert_dict = assert_is_san(activated=activate_assert_is_san(lessons))

    # to_dict = to_is_non(activated=activate_to_is_non(lessons))

    # wrapping_primitives_dict = wrapping_primitives_is_non(activated=activate_wrapping_primitives_is_non(lessons))

    # builtin_collection_dict = builtin_collection_is_non(activated=activate_builtin_collection_is_non(lessons))

    # get_post_select_dict = GET_POST_SELECT_is_sin_or_src(activated=activate_GET_POST_SELECT(lessons))

    getter_setter_dict = getter_setter_is_non(activated=True)

    hashCode_dict = hashCode_is_san(activated=True)

    assert_dict = assert_is_san(activated=True)

    to_dict = to_is_non(activated=True)

    wrapping_primitives_dict = wrapping_primitives_is_non(activated=True)

    builtin_collection_dict = builtin_collection_is_non(activated=True)

    get_post_select_dict = GET_POST_SELECT_is_sin_or_src(activated=True)


    return {**getter_setter_dict, **assert_dict, **to_dict, **wrapping_primitives_dict,
            **builtin_collection_dict, **get_post_select_dict, **hashCode_dict}


# main ====================================================
# =========================================================


def main(previous_graph_nodes, next_graph_nodes, lessons):
    """앞으로 적용할 evidence를 내놓는다."""

    global EXTRA_FEATURES_PREV
    global EXTRA_FEATURES_NEXT

    # 처음이라면 그럴 수 있어
    if previous_graph_nodes is None:
        return dict()

    # constant부터 초기화
    EXTRA_FEATURES_PREV = extra_features.main(previous_graph_nodes)
    EXTRA_FEATURES_NEXT = extra_features.main(next_graph_nodes)

    # 각각의 evidence들을 collect
    pairwise_similarity_dict = pairwise_similarity(lessons, next_graph_nodes)
    # one_call_dict = one_call_relation(lessons, next_graph_nodes)
    a_priori_dict = a_priori_rules(lessons, next_graph_nodes,
                                   EXTRA_FEATURES_PREV,
                                   EXTRA_FEATURES_NEXT)

    print("\npairwise_similarity_dict:", pairwise_similarity_dict, "\n") # TEMP
    print("a_priori_dict:", a_priori_dict, "\n") # TEMP

    # combined = {**pairwise_similarity_dict, **one_call_dict, **a_priori_dict}
    combined = {**pairwise_similarity_dict, **a_priori_dict}

    filtered = dict(filter(lambda tup: tup[0] in SKIP_FUNCS, combined.items()))

    # 그 evidence를 모두 합쳐서 내놓기
    return filtered
    # return combined
