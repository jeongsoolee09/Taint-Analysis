import csv
import json
import pandas as pd
import pickle
import matplotlib.pyplot as plt
import os.path
from pandarallel import pandarallel
from toolz import valfilter
from itertools import product, repeat


pandarallel.initialize()


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
    return True if value == "SwanFeatureExtractor.True" else False


# TODO: filter lambda functions
def normalize_featurevectors(df):
    # First, normalize the method names
    method_name = df.iloc[:, 0]
    methname_normalized = method_name.apply(normalize_methname)

    # Next, normalize the values
    rest = df.iloc[:, 1:]
    rest_normalized = rest.applymap(normalize_featurevalue)
    normalized_df = pd.concat([methname_normalized, rest_normalized], axis=1)

    # Drop the temporary lambda functions
    normalized_df = normalized_df[normalized_df["method_name"].map(lambda name: "$Lambda$" not in name) == True]
    return normalized_df


FEATURE_VECTORS = normalize_featurevectors(pd.read_csv(PROJECT_ROOT_DIR + "SwanFeatures.csv"))
FEATURE_VECTORS_without_name = FEATURE_VECTORS.drop("method_name", axis=1)
FEATURE_VECTORS_true_count = FEATURE_VECTORS.sum(axis=1)


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


def get_TrueFalse_ratio_one_column(colname):
    """Get the proportion of True values for a single column"""
    True_cnt, False_cnt, DontKnow_cnt = get_count_of_column(colname)
    return 0 if True_cnt == False_cnt == 0 else True_cnt / (True_cnt + False_cnt)


def get_TrueFalse_ratio_all_columns():
    """Get the proportion of True values for all columns and print it"""
    colnames = list(FEATURE_VECTORS.columns)[1:]
    for colname in colnames:
        ratio = get_TrueFalse_ratio_one_column(colname)
        print(colname, ":", ratio)

# Pairwise Similarity ===============================================
# ===================================================================

def get_score_by_column(colname):
    """Core idea: score columns with different scores.
       scoring scheme (if two feature value matches) based on T/F ratio:
       - 01_IsImplicitMethod (18%): score 72
       - 02_AnonymousClass (0.04%): score 99.96
       ...you get the idea, right?"""
    TF_ratio_percent = get_TrueFalse_ratio_one_column(colname) % 100
    return 100 * (1 - TF_ratio_percent)


def get_scores_of_columns():
    """Produce a mapping from colnames to their scores"""
    return dict([(colname, get_score_by_column(colname))
                 for colname in list(FEATURE_VECTORS.columns)])


# mapping from colnames to their scores
score_by_columns = get_scores_of_columns()


def get_scores_given_columns(colnames):
    """Given a list of colnames, find the similarity score."""
    acc = 0
    for colname in colnames:
        acc += score_by_columns[colname]
    return acc


# temp var for testing
testrow = FEATURE_VECTORS.iloc[303, :]


def get_true_columns(row):
    """Given a row, get the list of column names with True values."""
    to_dict = dict(row)
    True_keys = valfilter(lambda x: x, to_dict).keys()
    return list(True_keys)


def pairwise_sim(row):
    """get the scores of all rows regarding a single given row."""
    # Exclude the row in question
    FEATURE_VECTORS_other = FEATURE_VECTORS[FEATURE_VECTORS.method_name != row[0]]

    # Then, drop the "method_name" column (for convenient row-wise AND-ing)
    FEATURE_VECTORS_without_name = FEATURE_VECTORS_other.drop("method_name", axis=1)

    # The row in question, without the "method_name"
    row_without_name = row.drop("method_name")

    # Now, perform the row-wise AND
    anded = FEATURE_VECTORS_without_name.apply(lambda other_row: row_without_name & other_row)

    # Vector containing list of column names with True values, row by row.
    # NOTE This very likely is a bottleneck
    True_colnames_df = FEATURE_VECTORS_without_name.apply(lambda row: get_true_columns(row), axis=1)

    # Now, get the similarity scores based on the above colnames with True values
    sim_scores_df = True_colnames_df.apply(lambda row: get_scores_given_columns(row))

    # Append this to the FEAUTURE_VECTOR_other
    FEATURE_VECTORS_other["score"] = sim_scores_df

    # Retrieve rows with values greater than threshold
    threshold = 550  # TEMP: 나중에 따로 튜닝할 것.

    # Select the rows with scores higher than the threshold
    above_threshold_rows = FEATURE_VECTORS_other[FEATURE_VECTORS_other["score"] >= threshold]

    # Get the row indices selected above
    similar_row_indices = above_threshold_rows.index

    return list(similar_row_indices)


def score_all_rows():
    """Get the 'similar row indices' for all rows.
       NOTE This is a bottleneck: it takes 1min 37s using Intel i9"""
    # call pairwise_sim to every row of FEATURE_VECTORS
    similar_row_indices_df = FEATURE_VECTORS.parallel_apply(pairwise_sim, axis=1)
    similar_row_indices_df.to_csv("pairwise_sims.csv", mode="w+")


# Main ==============================================================
# ===================================================================

def main():
    score_all_rows()


if __name__ == "__main__":
    main()
