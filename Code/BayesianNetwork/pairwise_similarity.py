import json
import pandas as pd
import re
import os.path
import matplotlib.pyplot as plt
import time

from collections import Counter
from functools import reduce
from itertools import repeat
from pandarallel import pandarallel
from toolz import keymap, valfilter
from create_node import process


pandarallel.initialize()


# Utility Funcs ========================
# ======================================

NODE_DATA = pd.read_csv("nodes.csv", index_col=0)
DF = pd.read_csv("df.csv", index_col=0)
CALL = pd.read_csv("callg.csv", index_col=0)
CALLGRAPH = CALL[["id1", "id2"]]


def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]


PROJECT_ROOT_DIR = retrieve_path()


def load_chain_json():
    """Parse the whole Chain.json into a DataFrame"""
    path = os.path.join(PROJECT_ROOT_DIR, "Chain.json")
    return pd.read_json(path)


CHAIN = load_chain_json()


def filtermethod(string):
    return "$" not in string and\
           "__" not in string and\
           "<init>" not in string and\
           "<clinit>" not in string and\
           "lambda" not in string and\
           "Lambda" not in string


# https://stackoverflow.com/questions/29916065/how-to-do-camelcase-split-in-python
def camel_case_split(identifier):
    matches = re.finditer('.+?(?:(?<=[a-z])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])|$)', identifier)
    return [m.group(0) for m in matches]


# Syntactic Features =====================
# ========================================
# the parameter "node" stands for a row in NODE_DATA


def has_parameters(node):
    """Does this method have parameters?"""
    return node.intype != "void"


def has_return_type(node):
    """Does this method have a return type?"""
    return node.rtntype != "void"


def method_name_starts_with(node):
    """Extract the method name's prefix."""
    prefix = camel_case_split(node[3])[0]
    prefix = prefix.lower()
    return prefix


def method_name_contains(node):
    """Chop up the method name into words."""
    words = camel_case_split(node[3])
    words = list(map(lambda string: string.lower(), words))
    return words


def return_type_contains_name(node):
    """Chop up the return type into words."""
    words = camel_case_split(node[2])
    words = list(map(lambda string: string.lower(), words))
    return words


def class_contains_name(node):
    """Chop up the class name into words."""
    words = camel_case_split(node[2])
    words = list(map(lambda string: string.lower(), words))
    return words


def class_endswith_name(node):
    """Extract the class name's suffix."""
    words = camel_case_split(node[1])
    words = list(map(lambda string: string.lower(), words))
    suffix = words[len(words)-1]
    return suffix


def rtntype_equals(node):
    """Extract the return type of this method."""
    rtntype = node[2].lower()
    return rtntype


def param_contains_type_or_name(node):
    """Extract the input types of this method."""
    intypes = node[4].split(",")
    intypes = list(map(lambda string: string.lower(), intypes))
    return intypes


def param_type_matches_return_type(node):
    """Does any of the parameters match the return type?"""
    rtntype = node[2]
    intypes = node[4].split(",")
    return rtntype in intypes


def is_real_setter(node):
    """Feature that checks whether the current method begins with "get", and there
       is a corresponding "set" method in the class."""
    methname = node[3]
    classname = node[1]
    if camel_case_split(methname)[0] == "get":
        same_class_rows = NODE_DATA[NODE_DATA["class"] == classname]
        for row in same_class_rows.itertuples():
            other_name = row[4]
            if other_name == "set"+other_name[3:]:
                return True
        return False
    else:
        return False


def void_on_method(node):
    """Feature that matches whenever a method returns void and the method name starts
       with "on"."""
    return camel_case_split(node[3]) == "on" and node[2] == "void"


def method_name_contains_return_type(node):
    """Does the method name contain the return type?"""
    rtntype = node[2].lower()
    methname = node[3]
    return rtntype in list(map(lambda string: string.lower(),
                               camel_case_split(methname)))


# Semantic Features ==================
# ====================================


list_of_callers = list(CALLGRAPH["id1"])
list_of_callees = list(CALLGRAPH["id2"])
list_of_data_passers = list(DF["id1"])
list_of_data_passees = list(DF["id2"])


def invocation_name(node):
    """Get the Callees of this node."""
    meth_id = node[5]
    return CALLGRAPH[CALLGRAPH["id1"] == meth_id]["id2"].tolist()


def calling_but_no_df(node):
    """Is this method calling another method, but not passing any data to it?"""
    meth_id = node[5]
    node_is_caller = meth_id in list_of_callers
    not_passing_data = meth_id not in list_of_data_passers
    return node_is_caller and not_passing_data


def called_but_no_df(node):
    """Has this method been called, but are there no other data flowing into it?"""
    meth_id = node[5]
    node_is_callee = meth_id in list_of_callees
    not_being_passed_data = meth_id not in list_of_data_passees
    return node_is_callee and not_being_passed_data


def making_df_call(node):
    """Is this method calling other method and passing data at the same time?"""
    meth_id = node[5]
    node_is_caller = meth_id in list_of_callers
    passing_data = meth_id in list_of_data_passers
    return node_is_caller and passing_data


def has_df_call(node):
    """Is this method being called and being passed data at the same time?"""
    meth_id = node[5]
    node_is_callee = meth_id in list_of_callees
    being_passed_data = meth_id in list_of_data_passees
    return node_is_callee and being_passed_data


def receiving_and_passing_data(node):
    """Is this method receiving and passing data at the same time?"""
    meth_id = node[5]
    being_passed_data = meth_id in list_of_data_passees
    passing_data = meth_id in list_of_data_passers
    return being_passed_data and passing_data


# Borken
def has_df_call_and_dead(node):
    """Are any pieces of data being passed to this method via call
       and being dead in this method?"""
    meth_id = node[5]
    def mapfunc(chain):
        for event in chain:
            if event["status"] == "Dead":
                current_method = event["current_method"]
                for event in chain:
                    if event["status"] == "Call" and\
                       event["callee"] == current_method:
                        return True
        return False
    return CHAIN["chain"].apply(mapfunc).any()


def has_redefine(node):
    """Are there any data redefinitions in this method?"""
    meth_id = node[5]
    def mapfunc(chain):
        for event in chain:
            if event["status"] == "Redefine" and\
               event["current_method"] == meth_id:
                return True
        return False
    return CHAIN["chain"].apply(mapfunc).any()


# Batch run ==========================
# ====================================


def apply_and_concat():
    """parallel apply to NODE_DATA and concat them altogether"""
    id_df = pd.DataFrame(NODE_DATA["id"])
    id_df.columns = ["id"]

    # raw applied dataframes: before handling columns
    has_parameters_df = NODE_DATA.parallel_apply(has_parameters, axis=1)
    has_return_type_df = NODE_DATA.parallel_apply(has_return_type, axis=1)
    method_name_starts_with_df = NODE_DATA.parallel_apply(method_name_starts_with, axis=1)
    method_name_contains_df = NODE_DATA.parallel_apply(method_name_contains, axis=1)
    return_type_contains_name_df = NODE_DATA.parallel_apply(return_type_contains_name, axis=1)
    class_contains_name_df = NODE_DATA.parallel_apply(class_contains_name, axis=1)
    class_endswith_name_df = NODE_DATA.parallel_apply(class_endswith_name, axis=1)
    rtntype_equals_df = NODE_DATA.parallel_apply(rtntype_equals, axis=1)
    param_contains_type_or_name_df = NODE_DATA.parallel_apply(param_contains_type_or_name, axis=1)
    param_type_matches_return_type_df = NODE_DATA.parallel_apply(param_type_matches_return_type, axis=1)
    is_real_setter_df = NODE_DATA.parallel_apply(is_real_setter, axis=1)
    void_on_method_df = NODE_DATA.parallel_apply(void_on_method, axis=1)
    method_name_contains_return_type_df = NODE_DATA.parallel_apply(method_name_contains_return_type, axis=1)
    invocation_name_df = NODE_DATA.parallel_apply(invocation_name, axis=1)
    calling_but_no_df_df = NODE_DATA.parallel_apply(calling_but_no_df, axis=1)
    called_but_no_df_df = NODE_DATA.parallel_apply(called_but_no_df, axis=1)
    making_df_call_df = NODE_DATA.parallel_apply(making_df_call, axis=1)
    has_df_call_df = NODE_DATA.parallel_apply(has_df_call, axis=1)
    receiving_and_passing_data_df = NODE_DATA.parallel_apply(receiving_and_passing_data, axis=1)
    has_df_call_and_dead_df = NODE_DATA.parallel_apply(has_df_call_and_dead, axis=1)
    has_redefine_df = NODE_DATA.parallel_apply(has_redefine, axis=1)

    return pd.concat([ id_df,
                       has_parameters_df,
                       has_return_type_df,
                       method_name_starts_with_df,
                       method_name_contains_df,
                       return_type_contains_name_df,
                       class_contains_name_df,
                       class_endswith_name_df,
                       rtntype_equals_df,
                       param_contains_type_or_name_df,
                       param_type_matches_return_type_df,
                       is_real_setter_df,
                       void_on_method_df,
                       method_name_contains_return_type_df,
                       invocation_name_df,
                       calling_but_no_df_df,
                       called_but_no_df_df,
                       making_df_call_df,
                       has_df_call_df,
                       receiving_and_passing_data_df,
                       has_df_call_and_dead_df,
                       has_redefine_df ], axis=1)


FEATURE_VECTORS = apply_and_concat()


# Visualization Utilities ============
# ====================================

def get_count_of_column(colname):
    """한 column의 value의 분포를 pie chart로 visualize한다.
       parameter col의 input type: String"""
    # getting the proportion of Feature Values
    counts = FEATURE_VECTORS[colname].value_counts()
    True_cnt = counts.get(True)
    False_cnt = counts.get(False)
    if True_cnt is None:
        True_cnt = 0
    if False_cnt is None:
        False_cnt = 0

    return True_cnt, False_cnt


def visualize_single_page(colnames, index=1):
    """Visualize a single page with a given chunk of
       25 columns."""
    f, axes = plt.subplots(5, 5)
    colnames = iter(colnames)

    for i in range(5):
        for j in range(5):
            try:
                colname = next(colnames)
            except:
                return
            axes[i, j].set_title(colname)
            True_cnt, False_cnt = get_count_of_column(FEATURE_VECTORS, colname)
            # Parameters to .pie()
            group_sizes = [True_cnt, False_cnt]
            group_names = ["True", "False"]
            group_colors = []
            group_explodes = (0.1, 0)  # separate 1st slice
            axes[i, j].pie(group_sizes,
                           explode=group_explodes,
                           labels=group_names,
                           # autopct='%1.2f%%',
                           shadow=True,
                           startangle=90,
                           textprops={'fontsize': 7})
            # visualize the 25 subplots!
    plt.tight_layout()
    # plt.show()
    plt.savefig("{}.png".format(index))


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
    i = 1
    for column_chunk in column_chunks:
        visualize_single_page(FEATURE_VECTORS, column_chunk, i)
        i += 1


def get_TrueFalse_ratio_one_column(colname):
    """Get the proportion of True values for a single column"""
    True_cnt, False_cnt = get_count_of_column(colname)
    return 0 if True_cnt == False_cnt == 0 else True_cnt / (True_cnt + False_cnt)


def get_TrueFalse_ratio_all_columns():
    """Get the proportion of True values for all columns and print it"""
    colnames = list(FEATURE_VECTORS.columns)[1:]
    for colname in colnames:
        ratio = get_TrueFalse_ratio_one_column(colname)
        print(colname, ":", ratio)


# pairwise similarity =================
# =====================================


def make_scoring_function(this_row):
    def scoring_function(other_row):
        assert len(this_row) == len(other_row)
        score = 0
        for i in range(1, len(this_row)-1):  # to exclude the id column
            if type(this_row[i]) == bool or\
               type(this_row[i]) == str:
                assert type(this_row[i]) == type(other_row[i])
                if this_row[i] == other_row[i]:
                    score += 1
            elif type(this_row[i]) == list:
                for this_elem in this_row[i]:
                    for other_elem in other_row[i]:
                        if this_elem == other_elem:
                            score += 1
        return score
    return scoring_function


def fetch_methname_by_id(meth_id):
    return NODE_DATA[NODE_DATA.index == meth_id]["id"].iloc[0]


def get_similar_rows_score(this_row):
    """get the scores of all rows regarding a single given row, using an uneven scoring scheme."""
    # Exclude the row in question
    FEATURE_VECTORS_other = FEATURE_VECTORS[FEATURE_VECTORS["id"] != this_row["id"]]
    scoring_function = make_scoring_function(this_row)

    scores_series = FEATURE_VECTORS_other.apply(scoring_function, axis=1)

    threshold = 15              # TEMP

    scores_series_above_thres = scores_series.where(lambda score: (score > threshold)).dropna()
    converted_to_dict = scores_series_above_thres.to_dict()

    return keymap(fetch_methname_by_id, converted_to_dict)


def sort_dict_by_value_rev(dict_):
    return sorted(tuple(dict_.items()), key=lambda tup: tup[1], reverse=True)


def get_similar_rows_ranking(this_row):
    # Exclude the row in question
    FEATURE_VECTORS_other = FEATURE_VECTORS[FEATURE_VECTORS["id"] != this_row["id"]]
    scoring_function = make_scoring_function(this_row)

    scores_series = FEATURE_VECTORS_other.apply(scoring_function, axis=1)

    threshold_score = 15
    threshold_rank = 5

    scores_series_above_thres = scores_series.where(lambda score: (score > threshold_score)).dropna()

    converted_to_dict = scores_series_above_thres.to_dict()
    sorted_by_val = sort_dict_by_value_rev(converted_to_dict)
    cut = dict(sorted_by_val[:threshold_rank])

    return keymap(fetch_methname_by_id, cut)


def score_all_rows():
    """Get the 'similar row indices' for all rows.
       NOTE This is a bottleneck: it takes 60s using Intel i9"""
    # Call pairwise_sim to every row of FEATURE_VECTORS
    similar_row_indices_df = FEATURE_VECTORS.parallel_apply(get_similar_rows_ranking, axis=1)

    # and convert the resulting Series to a DataFrame
    similar_row_indices_df = pd.DataFrame(similar_row_indices_df)

    # Name the columns appropriately
    similar_row_indices_df = similar_row_indices_df.rename(columns={0: "similar_indices"})

    return similar_row_indices_df


def flatten_sim_df(sim_df):
    """Flatten a dataframe of dictionaries."""
    acc = pd.DataFrame([], columns=["class1", "rtntype1", "name1", "intype1", "id1",
                                    "class2", "rtntype2", "name2", "intype2", "id2", "score"])
    sim_df["id1"] = NODE_DATA["id"]
    def mapfunc(row):
        sim_dict = row[0]
        sim_tups = list(sim_dict.items())
        id1 = row[1]
        return pd.DataFrame([process(id1) + process(sim_tup[0]) + (sim_tup[1],) for sim_tup in sim_tups],
                            columns=["class1", "rtntype1", "name1", "intype1", "id1",
                                    "class2", "rtntype2", "name2", "intype2", "id2", "score"])
    for row in sim_df.itertuples(index=False):
        acc = pd.concat([acc, mapfunc(row)])
    acc = acc.reset_index(drop=True)
    return acc


# Finalizing DataFrame ================
# =====================================


def no_symmetric(dataframe):
    dataframe['temp'] = dataframe.index * 2
    dataframe2 = dataframe.iloc[:, [4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 10, 11]]
    dataframe2.columns = dataframe.columns
    dataframe2['temp'] = dataframe2.index * 2 + 1
    out = pd.concat([dataframe, dataframe2])
    out = out.sort_values(by='temp')
    out = out.set_index('temp')
    out = out.drop_duplicates()
    out = out[out.index % 2 == 0]
    out = out.reset_index().drop(columns=['temp'])
    return out


# main ================================
# =====================================


def main():
    start = time.time()

    pairwise_sims = no_symmetric(flatten_sim_df(score_all_rows()))
    pairwise_sims.to_csv("pairwise_sims.csv", mode="w+")

    print("elapsed time:", time.time()-start)


if __name__ == "__main__":
    main()
