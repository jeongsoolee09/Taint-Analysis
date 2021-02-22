import csv
import json
import modin.pandas as pd
import pickle
import matplotlib.pyplot as plt
import os.path
from itertools import product, repeat

# Constants =========================================================
# ===================================================================

def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]

PROJECT_ROOT_DIR = retrieve_path()

# Methods ===========================================================
# ===================================================================

def normalize_methname(methname):
    return methname.split("\"")[1]


def normalize_featurevalue(value):
    return value.split(".")[1]


def normalize_featurevectors(df):
    method_name = df.iloc[:, 0]
    rest = df.iloc[:, 1:]
    methname_normalized = method_name.apply(normalize_methname)
    rest_normalized = rest.applymap(normalize_featurevalue)
    return pd.concat([methname_normalized, rest_normalized], axis=1)


FEATURE_VECTORS = normalize_featurevectors(pd.read_csv(PROJECT_ROOT_DIR + "SwanFeatures.csv"))

# Visualization Utilities ===========================================
# ===================================================================

def get_count_of_column(colname):
    """한 column의 value의 분포를 pie chart로 visualize한다.
       parameter col의 input type: String"""
    # getting the proportion of Feature Values
    counts = FEATURE_VECTORS[colname].value_counts()
    True_cnt = counts.get("True")
    False_cnt = counts.get("False")
    DontKnow_cnt = counts.get("DontKnow")
    if True_cnt is None:
        True_cnt = 0
    if False_cnt is None:
        False_cnt = 0
    if DontKnow_cnt is None:
        DontKnow_cnt = 0

    return True_cnt, False_cnt, DontKnow_cnt


def visualize_single_page(colnames):
    """Visualize a single page with a given chunk of
       25 columns."""

    f, axes = plt.subplots(5, 5)
    colnames = iter(colnames)

    for i in range(5):
        for j in range(5):
            try:
                colname = next(colnames)
            except:
                pass
            axes[i, j].set_title(colname)
            True_cnt, False_cnt, DontKnow_cnt = get_count_of_column(colname)
            # Parameters to .pie()
            group_sizes = [True_cnt, False_cnt, DontKnow_cnt]
            group_names = ["True", "False", "DontKnow"]
            group_colors = []
            group_explodes = (0.1, 0, 0)  # separate 1st slice
            axes[i, j].pie(group_sizes,
                           explode=group_explodes,
                           labels=group_names,
                           # autopct='%1.2f%%',
                           shadow=True,
                           startangle=90,
                           textprops={'fontsize': 7})
            # visualize the 25 subplots!
    plt.tight_layout()
    plt.show()


def visualize_all_columns():
    # indices to place subplots
    # need to define a zipped list of colnames and page_nums
    acc = []                    # may change name
    colnames = list(FEATURE_VECTORS.columns)[1:]
    for i in range(7):
        acc += list(repeat(i, 25))
        colnames_and_pagenums = list(zip(colnames, acc))
        # now, partition these by pagenums
    acc = []
    for i in range(7):
        partition = list(filter(lambda tup: tup[1] == i, colnames_and_pagenums))
        acc.append(partition)
        column_chunks = list(map(lambda lst: list(map(lambda tup: tup[0], lst)), acc))
    for column_chunk in column_chunks:
        visualize_single_page(column_chunk)


# Pairwise Similarity ===============================================
# ===================================================================

def row_pairwise_sim(row):
    """주어진 row에 대해:
       1. True인 col들의 set을 찾는다. 이를 row_cols라 하자.
       2. 다른 각 row들에 대해:
          1. True인 col들의 set을 찾는다. 이를 other_cols라 하자.
          2. other_cols와 row_cols가 동일한지를 보자.
       3. other_cols와 row_cols가 동일한 것들을 리스트에 담아 낸다.
       NOTE 이걸 for-loop 없이 할 것."""



def pairwise_sim():
    """row_pairwise_sim을 각 row에 대해 모두 사용한다."""


def pickle():
    """pairwise_sim()의 결과물 dict를 피클링한다."""


# Main ==============================================================
# ===================================================================

def main():
    print("hihi")


if __name__ == "__main__":
    main()
