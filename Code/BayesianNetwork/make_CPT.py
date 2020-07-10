from z3 import *
from functools import reduce
import numpy as np
import pandas as pd

cpt_lookup_table = np.loadtxt("CPT_lookup_table.csv", delimiter=',')

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
def make_call_sim_mag_table(N):
    """parent가 쏜 엣지가 call/sim밖에 없을 때, magnitude table을 만든다."""
    arr = np.ones((4, 4**N)).astype(int)
    for (i,j), value in np.ndenumerate(arr):  # for efficient looping
        if label_identical(i, j, N):
            arr[i,j] = 2
        else:
            arr[i,j] = 4
    return arr


def make_df_mag_table(N):
    """parent가 쏜 엣지가 df밖에 없을 때, magnitude table을 만든다."""
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



def make_call_df_mag_table(edges):
    """parent가 쏜 엣지에 call/sim과 df가 섞여 있을 때, magnitude table을 만든다."""
    N = len(edges)
    df_CPT = make_df_mag_table(N)  # 먼저 df_CPT를 만들어 둔 다음
    parents_and_edges = list(zip(range(1, N+2), edges))  # n번째 parent와 그 엣지의 쌍들
    call_sim_parents = list(filter(lambda tup: tup[1] == "call" or
                                   tup[1] == "sim", parents_and_edges))
    call_sim_parents = list(map(lambda tup: tup[0], call_sim_parents))
    for (i,j), value in np.ndenumerate(df_CPT):
        cell_labels = labels_of(i, j, N)
        if to_be_mutated(cell_labels, call_sim_parents):
            if df_CPT[i,j] == 4:  # White였다면, Green으로 바꿔 줌
                df_CPT[i,j] = 3
            else:  # Yellow였다면, Yellow-Green으로 바꿔 줌
                df_CPT[i,j] = 1
    return df_CPT


def base_5_tup_to_decimal(tup):
    return tup[0]*125+tup[1]*25+tup[2]*5+tup[3]


def get_row_of_lookup_table(tup):
    """column 값이 들어 있는 4개짜리 튜플을 받아서, lookup table의 몇 번째 행에 접근하면 되는지를 파악한다."""
    only_labels = cpt_lookup_table[:,:4]
    ndarray_slice = np.asarray(tup)
    broadcasted = only_labels == ndarray_slice
    return np.where(np.all(broadcasted, axis=1))[0][0]


def make_CPT(cpt_kind, edges):
    """CPT의 종류와, 엣지들의 종류 목록에 따라 CPT를 만든다. 가능한 CPT의 종류:
       1. call_df (혹은 df_call)
       2. df
       3. call_sim"""
    if cpt_kind == "call_df" or cpt_kind == "df_call":
        mag_table = make_call_df_mag_table(edges)
    elif cpt_kind == "df":
        mag_table = make_df_mag_table(len(edges))
    elif cpt_kind == "call_sim":
        mag_table = make_call_sim_mag_table(len(edges))
    _, cols = mag_table.shape
    out = []
    for col in range(cols):
        col_tuple = (mag_table[0][col], mag_table[1][col], mag_table[2][col], mag_table[3][col])
        lookup_table_row = cpt_lookup_table[get_row_of_lookup_table(col_tuple)]
        lookup_table_row = lookup_table_row[4:8]
        out.append(lookup_table_row)
    out = np.asarray(out).transpose()
    return out
