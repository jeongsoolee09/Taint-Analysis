from z3 import *
from functools import reduce
import numpy as np

"""너무 모든 것을 Z3에 맡기려다 보니 문제 풀기가 어려워졌다. 특히, 어떤 조건 하에서 cell이 어떤 magnitude를 가지는지를 Z3로 풀려다 보니 특히 어려워진 것. 그 부분을 순정 파이썬+numpy로 메꾸려 한다. 쉽게 가즈아"""

MAGNITUDE = ["YG", "Y", "G", "W"]
LABELDICT = {1: "src", 2: "sin", 3: "san", 4: "non"}
MAGDICT = {1: "YG", 2: "Y", 3: "G", 4: "W"}

# CPT를 만들되, 개략적인 magnitude만 들어가 있게끔 만든다.


def labels_of(row, column, N):
    """set the label of all parents and child a cell represents, given the cell's index and the total number of parents"""
    out = []
    for parent_count in range(1, N+1):
        parent_label = ((column//(4**(N-parent_count))) % 4) + 1
        out.append((parent_count, parent_label))
    child_label = row+1
    out.append((N+1, child_label))  # the last pair refers to the child
    return out

# https://stackoverflow.com/questions/3844801/check-if-all-elements-in-a-list-are-identical
def elements_are_identical(iterator):
    """check if all elements in are identical with one another"""
    iterator = iter(iterator)
    try:
        first = next(iterator)
    except StopIteration:
        return True
    return all(first == rest for rest in iterator)


def label_identical(row, column, N):
    """Returns True if the cell's parents and child have identical labels, False otherwise"""
    node_with_labels = labels_of(row, column, N)
    labels = list(map(lambda tup: tup[1], node_with_labels))
    return elements_are_identical(labels)


# Core functions
def make_call_sim_CPT(N):
    arr = np.ones((4, 4**N)).astype(int)
    for (i,j), value in np.ndenumerate(arr):  # for efficient looping
        if label_identical(i, j, N):
            arr[i,j] = 2
        else:
            arr[i,j] = 4
    return arr


def make_df_CPT(N):
    arr = np.ones((4, 4**N)).astype(int)
    for (i,j), value in np.ndenumerate(arr):  # for efficient looping
        parent_labels = labels_of(i, j, N)
        parent_labels = list(map(lambda tup: tup[1], parent_labels))
        child_label = parent_labels.pop()
        if 2 in parent_labels:
            arr[i, j] = 4
        elif 3 in parent_labels:
            if child_label == 1 or child_label == 3:
                arr[i, j] = 4
            else:
                arr[i, j] = 2
        else:
            if child_label == 1:
                arr[i, j] = 4
            else:
                arr[i, j] = 2
    return arr


def to_be_mutated(labels, call_sim_parents):
    """어떤 셀을 G 혹은 YG로 칠할 것인지 정하기 위해, call_sim_parents의 레이블이 모두 같고, 이 레이블과 child의 레이블이 같은지를 판단한다."""
    child_label_tup = labels.pop()
    labels = list(filter(lambda tup: tup[0] in call_sim_parents, labels))
    labels = list(map(lambda tup: tup[1], labels))  # leave labels only
    if elements_are_identical(labels):
        if child_label_tup[1] == labels[0]:  # child's label is also same
            return True
        else:  # child's label does not agree
            return False
    else:
        return False



def make_call_df_CPT(edges):
    """df랑 call/sim이 섞여 있기 때문에 어떤 parent와 어떤 edge가 연관되어 있는가의 정보가 주어져야 함"""
    N = len(edges)
    df_CPT = make_df_CPT(N)  # 먼저 df_CPT를 만들어 둔 다음
    parents_and_edges = list(zip(range(1, N+2), edges))  # n번째 parent와 그 엣지의 쌍들
    call_sim_parents = list(filter(lambda tup: tup[1] == "call" or
                                   tup[1] == "sim", parents_and_edges))
    call_sim_parents = list(map(lambda tup: tup[0], call_sim_parents))
    print(parents_and_edges)
    print(call_sim_parents)
    for (i,j), value in np.ndenumerate(df_CPT):
        cell_labels = labels_of(i, j, N)
        if to_be_mutated(cell_labels, call_sim_parents):
            if df_CPT[i,j] == 4:  # White였다면, Green으로 바꿔 줌
                df_CPT[i,j] = 3
            else:  # Yellow였다면, Yellow-Green으로 바꿔 줌
                df_CPT[i,j] = 1
