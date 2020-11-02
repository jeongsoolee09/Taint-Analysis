# 백지 상태에서 시작하지 않고, 이전 경험에서부터 배우도록 하자.
import networkx as nx
import pandas as pd
import extra_features
import re

from operator import itemgetter
from split_underlying_graph import draw_callgraph
from create_edge import no_symmetric
from create_node import process

# Constants ============================================
# ======================================================

SIM_VECTORS = pd.read_csv("sim_vectors.csv", index_col=0)
CALLGRAPH = nx.read_gpickle("callgraph")
EXTRA_FEATURES_PREV = None      # extra features for previous graph
EXTRA_FEATURES_NEXT = None      # extra features for next graph

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
    oracle_response = dict(find_oracle_response(final_snapshot, current_asked))
    conf_sols = dict(find_conf_sols(final_snapshot, current_asked))
    previous_lessons_nodes = {**oracle_response, **conf_sols}
    return {**previous_lessons, **previous_lessons_nodes}


def convert_bool_to_int(df):
    df = df.replace(['True'], [1])
    df = df.replace([True], [1])
    df = df.replace(['False'], [0])
    df = df.replace([False], [0])
    return df


def scoring_function(node1, node2):
    """cartesian product의 한 row를 받아서 두 node가 충분히 similar한지 판단하는 메소드"""
    # node1의 feature vector를 retrieve
    node1_vector = SIM_VECTORS.loc[SIM_VECTORS['id'] == node1]
    node1_vector = node1_vector.drop(columns=['id'])

    # node2의 feature vector를 retrieve
    node2_vector = SIM_VECTORS.loc[SIM_VECTORS['id'] == node2]
    node2_vector = node2_vector.drop(columns=['id'])

    node1_vector = convert_bool_to_int(node1_vector)
    node2_vector = convert_bool_to_int(node2_vector)

    elementwise_and = node1_vector & node2_vector

    true_count = elementwise_and.sum().sum()

    return True if true_count >= 2 else False


# Tentative rule activator ===================================
# ============================================================


def activate_getter_setter(lessons):
    """previous_lessons_nodes에 getter/setter가 포함되어 있는지, 확인"""
    for node, label in lessons.items():
        row = EXTRA_FEATURES_PREV[EXTRA_FEATURES_PREV['name']==node]
        if row["getter_setter"] == "getter" or\
           row["getter_setter"] == "setter":
            if label == "non":
                return True         # 거봐 내 말이 맞다니까
        else:
            continue                # 두고 봐 진짜라니까


def activate_hashCode_is_san(lessons):
    """lessons에 hashCode가 포함되어 있는지를 확인"""
    for node, label in lessons.items():
        row = EXTRA_FEATURES_PREV[EXTRA_FEATURES_PREV['name']==node]
        if row["is_hashCode"]:
            if label == 'san':
                return True     # 거봐 내 말이 맞다니까
        else:
            continue            # 두고 봐 진짜라니까


def activate_assert_is_san(lessons):
    """lessons에 assert*가 포함되어 있는지를 확인"""
    for node, label in lessons.items():
        row = EXTRA_FEATURES_PREV[EXTRA_FEATURES_PREV['name']==node]
        if row["is_assert"]:
            if label == 'san':
                return True     # 거봐 내 말이 맞다니까
        else:
            continue            # 두고 봐 진짜라니까


def activate_to_is_non(lessons):
    """# lessons에 is*가 포함되어 있는지를 확인"""
    for node, label in lessons.items():
        row = EXTRA_FEATURES_PREV[EXTRA_FEATURES_PREV['name']==node]
        if row["is_to"]:
            if label == "non":
                return True
        else:
            continue


def activate_wrapping_primitives_is_non(lessons):
    """lessons에 primitive 타입을 wrapping하는 클래스 메소드가 포함되어 있는지를 확인"""
    for node, label in lessons.items():
        row = EXTRA_FEATURES_PREV[EXTRA_FEATURES_PREV['name']==node]
        if row["is_wrapping_primitive"]:
            if label == "non":
                return True
        else:
            continue


def activate_builtin_collection_is_non(lessons):
    """lessons에 builtin collection 클래스 메소드가 포함되어 있는지를 확인"""
    for node, label in lessons.items():
        row = EXTRA_FEATURES_PREV[EXTRA_FEATURES_PREV['name']==node]
        if row["is_builtin_coll"]:
            if label == "non":
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
                learned[method_name] = 'non'
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
                learned[method_name] = "san"
    else:
        return dict()


def assert_is_san(**kwargs):
    """다음에 사용될 노드들 중에서 is로 시작하는 메소드들에 대해 미리 문답을 해 놓는다."""
    if kwargs["activated"]:
        learned = dict()
        for row in EXTRA_FEATURES_NEXT.itertuples():
            method_name = row[1]
            if "assert" in method_name:
                learned[method_name] = "san"
    else:
        return dict()


def to_is_non(**kwargs):
    """다음에 사용될 노드들 중에서 to로 시작하는 메소드들에 대해 미리 문답을 해 놓는다."""
    if kwargs["activated"]:
        learned = dict()
        for row in EXTRA_FEATURES_NEXT.itertuples():
            method_name = row[1]
            if "is" == camel_case_split(method_name)[0]:
                learned[method_name] = "non"
    else:
        return dict()


def wrapping_primitives_is_non(**kwargs):
    """다음에 사용될 노드들 중에서 primitive를 wrapping하는 메소드들에 대해 미리 문답을 해 놓는다."""
    if kwargs["activated"]:
        learned = dict()
        for row in EXTRA_FEATURES_NEXT.itertuples():
            method_name = row[1]
            if row[6]:
                learned[method_name] = 'non'
    else:
        return dict()


def builtin_collection_is_non(**kwargs):
    """다음에 사용될 노드들 중에서 builtin collection class의 메소드들에 대해 미리 문답을 해 놓는다."""
    if kwargs["activated"]:
        learned = dict()
        for row in EXTRA_FEATURES_NEXT.itertuples():
            method_name = row[1]
            if row[7]:
                learned[method_name] = 'non'
    else:
        return dict()


# evidence builders ==========================================
# ============================================================

def pairwise_similarity(lessons_nodes, state_names):
    """lessons의 내용을 보고, state_names 중에서 충분히 닮은 것들을 찾아낸다."""
    global EXTRA_FEATURES_PREV
    global EXTRA_FEATURES_NEXT

    # 맨 처음 loop을 돌 때는 lesson이 안 쌓여 있기 때문
    if lessons_nodes == dict():
        return dict()

    # 충분히 similar한 것들 찾아내기

    # 전처리: (class, rtntype, methodname, intype, id)의 튜플 리스트로 만들기
    previous_lessons_nodes = list(lessons_nodes.keys())
    previous_lessons_nodes = list(map(process, previous_lessons_nodes))

    state_names = list(map(process, state_names))

    # 두 개의 DF를 준비: 이전의 오라클 답변들과 현재 그래프의 노드 이름들
    previous_lessons_nodes = pd.DataFrame(previous_lessons_nodes)  # 이전의 오라클 답변들
    state_names = pd.DataFrame(state_names)         # 다음에 갈아끼울 BN state 이름들

    previous_lessons_nodes.columns = ['class', 'rtntype', 'name', 'intype', 'id']
    state_names.columns = ['class', 'rtntype', 'name', 'intype', 'id']

    # 그 두 DF의 Cartesian Product를 제작
    previous_lessons_nodes['key'] = 1
    state_names['key'] = 1
    carPro = pd.merge(previous_lessons_nodes, state_names, how='outer', on=['key'])
    carPro = carPro.drop("key", axis=1)
    carPro.columns = ['class1', 'rtntype1', 'name1', 'intype1', 'id1',
                      'class2', 'rtntype2', 'name2', 'intype2', 'id2']

    # make a label column
    mapfunc = lambda row: lessons_nodes[row['id1']]
    labels = carPro.apply(mapfunc, axis=1)
    carPro['labels'] = labels

    # filter rows without sufficient similarity
    mapfunc = lambda row: scoring_function(row['id1'], row['id2'])
    bool_df = carPro.apply(mapfunc, axis=1)
    carPro['leave'] = bool_df

    carPro = carPro[carPro.leave != False]
    carPro = carPro.drop(columns=['leave'])

    carPro = carPro.drop(columns=['class1', 'rtntype1', 'name1', 'intype1', 'id1', 
                                  'class2', 'rtntype2', 'name2', 'intype2'])

    similars = carPro.to_dict('split')['data']
    similars = dict(similars)

    # 1-call 관계에 있는 노드들 찾아내기
    # lesson에 있는 노드와 1-call 관계에 있으면서 state_names에 동시에 있는 노드들 찾아내기

    return similars


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
            label = lesson_nodes[edge2]
            if edge1 in state_names:
                one_call_nodes.append((edge1, label))

    one_call_nodes = dict(one_call_nodes)

    out = {**similars, **one_call_nodes}

    return out


def a_priori_rules(lessons, state_names):  #  여기서 state_names는 그 다음에 물어볼 그래프의 노드들의 이름들.
    """굳이 물어보지 않아도 아는 것들: activate된 tentative rule들을 바탕으로, 해당되는 노드들을 찾아낸다."""
    # tentative rule들을 사용한다.
    getter_setter_dict = getter_setter_is_non(activated=activate_getter_setter(lessons))
    hashCode_dict = hashCode_is_san(activated=activate_hashCode_is_san(lessons))
    assert_dict = assert_is_san(activated=activate_assert_is_san(lessons))
    to_dict = to_is_non(activated=activate_assert_is_non(lessons))
    wrapping_primitives_dict = wrapping_primitives_is_non(activated=activate_wrapping_primitives_is_non(lessons))
    builtin_collection_dict = builtin_collection_is_non(activated=activate_builtin_collection_is_non(lessons))
    return {**getter_setter_dict, **hashCode_dict, **assert_dict,
             **to_dict, **wrapping_primitives_dict, **builtin_collection_dict}


# main ====================================================
# =========================================================


def main(previous_graph, next_graph, lessons, state_names):
    # constant부터 초기화
    EXTRA_FEATURES_PREV = extra_features.main(previous_graph)
    EXTRA_FEATURES_NEXT = extra_features.main(next_graph)

    ps_dict = pairwise_similarity(lessons, state_names)
    one_call_dict = one_call_relation(lessons, state_names)
    a_priori_dict = a_priori_rules(lessons, state_names)

    return {**ps_dict, **one_call_dict, **a_priori_dict}
