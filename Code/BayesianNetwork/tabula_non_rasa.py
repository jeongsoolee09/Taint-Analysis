# 백지 상태에서 시작하지 않고, 이전 경험에서부터 배우도록 하자.
import networkx as nx
import pandas as pd

from operator import itemgetter
from split_underlying_graph import draw_callgraph

# Constants ============================================
# ======================================================

CALLGRAPH = draw_callgraph()
SIM_EDGES = pd.read_csv("sim.csv")

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
    lessons = {**oracle_response, **conf_sols}
    return {**previous_lessons, **lessons}


# lessons의 내용을 보고, state_names 중에서 충분히 닮은 것들, 그리고 1-call 관계에 있는 노드들을 찾아낸다.
def make_evidence(lessons, state_names):
    previous_lessons_nodes = pd.DataFrame(lessons.keys())

    ### state_names 중에서 충분히 닮은 것들을 찾기: 기존의 similarity 기준 사용
    state_names = pd.DataFrame(state_names)

    previous_lessons_nodes['key'] = 1
    state_names['key'] = 1
    carPro = pd.merge(previous_lessons_nodes, state_names, how="outer")
    carPro = carPro.drop('key', axis=1)

    ### 1-call 관계에 있는 노드들 찾기
    
