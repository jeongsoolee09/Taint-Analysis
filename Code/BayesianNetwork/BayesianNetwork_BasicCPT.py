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
def check_if_unique(iterator):
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
    return check_if_unique(labels)


# Core functions
def make_call_sim_CPT(N):
    arr = np.ones((4, 4**N)).astype(int)
    for (i,j), value in np.ndenumerate(arr):  # for efficient looping
        if label_identical(i, j, N):
            arr[i,j] = 2
        else:
            arr[i,j] = 4
    print(arr)


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
    print(arr)
 

def make_call_df_CPT():
    pass
