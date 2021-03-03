import pandas as pd
import time
import os.path
import json
import csv

from create_node import process
from itertools import repeat


# Constants ==================================================
# ============================================================


def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]


PROJECT_ROOT_DIR = retrieve_path()


def normalize_methname(methname):
    return methname.split("\"")[1]


def normalize_featurevalue(value):
    return True if value == "SwanFeatureExtractor.True" else False


def normalize_featurevectors(df):
    # First, normalize the method names
    method_name = df.iloc[:, 0]
    methname_normalized = method_name.apply(normalize_methname)

    # Next, normalize the values
    rest = df.iloc[:, 1:]
    rest_normalized = rest.applymap(normalize_featurevalue)
    normalized_df = pd.concat([methname_normalized, rest_normalized], axis=1)

    # Drop the temporary lambda functions
    normalized_df = normalized_df[normalized_df["method_name"].map(lambda name: "Lambda" not in name and\
                                                                   "lambda" not in name) == True]
    return normalized_df


FEATURE_VECTORS = normalize_featurevectors(pd.read_csv(PROJECT_ROOT_DIR + "SwanFeatures.csv"))


def lookup_by_index(index):
    """looks up FEATURE_VECTORS with the index,
       retrieving its corresponding method_id"""
    return FEATURE_VECTORS.loc[index].method_name


def get_method_ids_for_indices(index_list_str):
    """given a row, convert all similar_row_indices with their method_ids"""
    index_list = eval(index_list_str)
    return list(map(lookup_by_index, index_list))


def prepare_pairwise_sims():
    """prepare the PAIRWISE_SIMS DataFrame."""
    raw = pd.read_csv("pairwise_sims.csv")

    # convert the method indices into method ID strings
    method_ids = raw["Unnamed: 0"].map(lookup_by_index)
    similar_method_ids = raw["similar_indices"].map(get_method_ids_for_indices)

    # concat the columns
    raw["method_id"] = method_ids
    raw["similar_methods"] = similar_method_ids

    # drop the stale columns
    raw = raw.drop("Unnamed: 0", axis=1)
    raw = raw.drop("similar_indices", axis=1)

    return raw


# PAIRWISE_SIMS = pd.read_csv("pairwise_sims.csv").set_index("Unnamed: 0")\
#                                                 .apply(get_method_ids_for_indices, axis=1)

PAIRWISE_SIMS = prepare_pairwise_sims()


# DataFrame assemblers =======================================
# ============================================================


def make_dataframes():
    methodInfo1 = pd.read_csv("nodes.csv", index_col=0)
    methodInfo2 = pd.read_csv("nodes.csv", index_col=0)
    methodInfo1 = methodInfo1.rename(columns={'index': 'index1', 'class': 'class1',
                                              'rtntype': 'rtntype1', 'name': 'name1',
                                              'intype': 'intype1', 'id': 'id1'})
    methodInfo2 = methodInfo2.rename(columns={'index': 'index2', 'class': 'class2',
                                              'rtntype': 'rtntype2', 'name': 'name2',
                                              'intype': 'intype2', 'id': 'id2'})
    methodInfo1['key'] = 1
    methodInfo2['key'] = 1
    carPro = pd.merge(methodInfo1, methodInfo2, how='outer')
    carPro = carPro.drop('key', axis=1)
    methodInfo1 = methodInfo1.rename(columns={'index1': 'index', 'class1': 'class',
                                              'rtntype1': 'rtntype', 'name1': 'name',
                                              'intype1': 'intype', 'id1': 'id'})
    methodInfo2 = methodInfo2.rename(columns={'index2': 'index', 'class2': 'class',
                                              'rtntype2': 'rtntype', 'name2': 'name',
                                              'intype2': 'intype', 'id2': 'id'})
    return methodInfo1, methodInfo2, carPro


def filtermethod(string):
    return "__" not in string and\
        "<init>" not in string and\
        "<clinit>" not in string and\
        "lambda" not in string and\
        "Lambda" not in string


def load_chain_json():
    """Parse the whole Chain.json into a list"""
    path = os.path.join(PROJECT_ROOT_DIR, "Chain.json")
    with open(path, "r+") as chainjson:
        wrapped_chain_list = json.load(chainjson)
    return wrapped_chain_list


def make_calledges():
    path = os.path.join(PROJECT_ROOT_DIR, "Callgraph.txt")
    with open(path, "r+") as callgraphfile:
        lines = callgraphfile.readlines()
        lines = list(filter(filtermethod, lines))
        lines = list(map(lambda line: line.rstrip(), lines))
        lines = list(map(lambda line: line.split(" -> "), lines))
        call_edges = list(map(lambda lst: tuple(lst), lines))
        call_edges = list(map(lambda tup: (process(tup[0]), process(tup[1])), call_edges))
    return call_edges


def detect_dataflow(json_obj_list):
    dataflow_edges = []
    for wrapped_chain in json_obj_list:
        for activity_repr in wrapped_chain['chain']:
            if activity_repr['status'] == 'Call':
                caller_name = activity_repr['current_method']
                callee_name = activity_repr['callee']
                dataflow_edges.append((caller_name, callee_name))
            if activity_repr['status'] == 'Define':
                caller_name = activity_repr['current_method']
                callee_name = activity_repr['using']
    dataflow_edges.append((caller_name, callee_name))
    dataflow_edges = list(filter(lambda tup: '' not in tup, dataflow_edges))
    dataflow_edges = list(filter(lambda tup: filtermethod(tup[0]) and filtermethod(tup[1]), dataflow_edges))
    dataflow_edges = list(map(lambda tup: (process(tup[0]), process(tup[1])), dataflow_edges))
    return dataflow_edges


def make_df_dataframe(dataflow_edges):
    """edges.csv에서의 data flow row를 만든다: tuple list를 dataframe으로 변환."""
    class1, rtntype1, name1, intype1, id1,\
        class2, rtntype2, name2, intype2, id2 = [], [], [], [], [], [], [], [], [], []
    for parent, child in dataflow_edges:

        class1.append(parent[0])
        rtntype1.append(parent[1])
        name1.append(parent[2])
        intype1.append(parent[3])
        id1.append(parent[4])

        class2.append(child[0])
        rtntype2.append(child[1])
        name2.append(child[2])
        intype2.append(child[3])
        id2.append(child[4])

    return pd.DataFrame({'class1': class1, 'rtntype1': rtntype1, 'name1': name1, 'intype1': intype1, 'id1': id1,
                         'class2': class2, 'rtntype2': rtntype2, 'name2': name2, 'intype2': intype2, 'id2': id2})


def make_call_dataframe(call_edges):
    """edges.csv에서의 call row를 만든다: tuple list를 dataframe으로 변환."""
    class1, rtntype1, name1, intype1, id1,\
        class2, rtntype2, name2, intype2, id2 = [], [], [], [], [], [], [], [], [], []
    for parent, child in call_edges:
        class1.append(parent[0])
        rtntype1.append(parent[1])
        name1.append(parent[2])
        intype1.append(parent[3])
        id1.append(parent[4])

        class2.append(child[0])
        rtntype2.append(child[1])
        name2.append(child[2])
        intype2.append(child[3])
        id2.append(child[4])

    return pd.DataFrame({'class1': class1, 'rtntype1': rtntype1, 'name1': name1, 'intype1': intype1, 'id1': id1,
                         'class2': class2, 'rtntype2': rtntype2, 'name2': name2, 'intype2': intype2, 'id2': id2})


def make_sim_dataframe():
    """Re-express PAIRWISE_SIMS into format identical to df_dataframe and call_dataframe"""
    class1, rtntype1, name1, intype1, id1,\
        class2, rtntype2, name2, intype2, id2 = [], [], [], [], [], [], [], [], [], []
    tuple_acc = []
    iterator = PAIRWISE_SIMS.itertuples(index=False)

    while True:
        try:
            method_id, similar_methods = next(iterator)
        except StopIteration:
            break

        if similar_methods == []:
            continue

        info1 = process(method_id)

        for similar_method in similar_methods:
            info2 = process(similar_method)
            tuple_acc.append(info1 + info2)

    return pd.DataFrame(tuple_acc, columns=["class1", "rtntype1", "name1", "intype1", "id1",
                                            "class2", "rtntype2", "name2", "intype2", "id2"])


def merge_dataframes(df_dataframe, call_dataframe, sim_dataframe):
    """df, call, sim dataframe 세 개를 하나로 합친다."""
    return df_dataframe.append(call_dataframe).append(sim_dataframe)


def multiindex_edges(edges):
    """edges dataframe이 주어졌을 때, 그 dataframe을 multiindex로 바꾼다."""
    edge1_high = list(repeat('edge1', 5))
    edge2_high = list(repeat('edge2', 5))
    high_edges = edge1_high + edge2_high
    edge1_index = list(edges.columns)[0:6]
    edge1_index = list(map(lambda index: index[0:len(index)-1], edge1_index))
    edge2_index = list(edges.columns)[6:12]
    edge2_index = list(map(lambda index: index[0:len(index)-1], edge2_index))
    low_edges = edge1_index + edge2_index
    tuples = list(zip(high_edges, low_edges))
    index = pd.MultiIndex.from_tuples(tuples)
    edges.columns = index
    return edges


def no_symmetric(dataframe):
    dataframe['temp'] = dataframe.index * 2
    dataframe2 = dataframe.iloc[:, [4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 10]]
    dataframe2.columns = dataframe.columns
    dataframe2['temp'] = dataframe2.index * 2 + 1
    out = pd.concat([dataframe, dataframe2])
    out = out.sort_values(by='temp')
    out = out.set_index('temp')
    out = out.drop_duplicates()
    out = out[out.index % 2 == 0]
    out = out.reset_index().drop(columns=[('temp', '')])
    return out


def no_reflexive(dataframe):
    cond1 = dataframe[('edge1', 'class')] != dataframe[('edge2', 'class')]
    cond2 = dataframe[('edge1', 'rtntype')] != dataframe[('edge2', 'rtntype')]
    cond3 = dataframe[('edge1', 'name')] != dataframe[('edge2', 'name')]
    cond4 = dataframe[('edge1', 'intype')] != dataframe[('edge2', 'intype')]
    return dataframe[cond1 | cond2 | cond3 | cond4]


def test_reflexive(dataframe):
    reflex1 = dataframe[('edge1', 'class')] == dataframe[('edge2', 'class')]
    reflex2 = dataframe[('edge1', 'rtntype')] == dataframe[('edge2', 'rtntype')]
    reflex3 = dataframe[('edge1', 'name')] == dataframe[('edge2', 'name')]
    reflex4 = dataframe[('edge1', 'intype')] == dataframe[('edge2', 'intype')]
    return dataframe[reflex1 & reflex2 & reflex3 & reflex4]


def output_alledges(dataflow_dataframe, call_dataframe, sim_dataframe):
    dataflow_dataframe.to_csv("df.csv", mode='w+')
    call_dataframe.to_csv("callg.csv", mode='w+')
    sim_dataframe.to_csv("sim.csv", mode='w+')


# Main =======================================================
# ============================================================


def main():
    start = time.time()

    methodInfo1, methodInfo2, carPro = make_dataframes()  # the main data we are manipulating
    json_obj_list = load_chain_json()
    dataflow_edges = detect_dataflow(json_obj_list)
    call_edges = make_calledges()

    dataflow_dataframe = make_df_dataframe(dataflow_edges)
    call_dataframe = make_call_dataframe(call_edges)
    sim_dataframe = make_sim_dataframe()

    edges_dataframe = merge_dataframes(dataflow_dataframe, call_dataframe, sim_dataframe)
    edges_dataframe = multiindex_edges(edges_dataframe)
    edges_dataframe = edges_dataframe.reset_index().drop(columns=[('index', '')])

    edges_dataframe = no_symmetric(edges_dataframe)
    edges_dataframe = no_reflexive(edges_dataframe)

    edges_dataframe.to_csv("edges.csv", mode='w+')

    output_alledges(dataflow_dataframe, call_dataframe, sim_dataframe)
    print("elapsed time:", time.time()-start)


if __name__ == "__main__":
    main()
