import pandas as pd
import time
import os.path
import json
import csv

from multiprocessing import Pool
from create_node import process
from itertools import repeat


def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]


PROJECT_ROOT_PATH = retrieve_path()


def make_dataframes():
    methodInfo1 = pd.read_csv("nodes.csv", index_col=0)
    methodInfo2 = pd.read_csv("nodes.csv", index_col=0)
    methodInfo1 = methodInfo1.rename(columns={'index':'index1', 'class':'class1',
                                              'rtntype':'rtntype1', 'name':'name1',
                                              'intype':'intype1', 'id':'id1'})
    methodInfo2 = methodInfo2.rename(columns={'index':'index2', 'class':'class2',
                                              'rtntype':'rtntype2', 'name':'name2',
                                              'intype':'intype2', 'id':'id2'})
    methodInfo1['key'] = 1
    methodInfo2['key'] = 1
    carPro = pd.merge(methodInfo1, methodInfo2, how='outer')
    carPro = carPro.drop('key', axis=1)
    methodInfo1 = methodInfo1.rename(columns={'index1':'index', 'class1':'class',
                                              'rtntype1':'rtntype', 'name1':'name',
                                              'intype1':'intype', 'id1':'id'})
    methodInfo2 = methodInfo2.rename(columns={'index2':'index', 'class2':'class',
                                              'rtntype2':'rtntype', 'name2':'name',
                                              'intype2':'intype', 'id2':'id'})
    return methodInfo1, methodInfo2, carPro


def filtermethod(string):
    return "$" not in string and\
           "__" not in string and\
           "<init>" not in string and\
           "<clinit>" not in string and\
           "lambda" not in string and\
           "Lambda" not in string


def load_chain_json():
    """Chain.json을 통째로 파싱해 파이썬 자료구조에 담는다. 결과값은 리스트이다."""
    path = os.path.join(PROJECT_ROOT_PATH, "Chain.json")
    with open(path, "r+") as chainjson:
        wrapped_chain_list = json.load(chainjson)
    return wrapped_chain_list


def make_calledges():
    path = os.path.join(PROJECT_ROOT_PATH, "Callgraph.txt")
    with open(path, "r+") as callgraphfile:
        lines = callgraphfile.readlines()
        lines = list(filter(filtermethod, lines))
        lines = list(map(lambda line: line.rstrip(), lines))
        lines = list(map(lambda line: line.split(" -> "), lines))
        call_edges = list(map(lambda lst: tuple(lst), lines))
        call_edges = list(map(lambda tup: (process(tup[0]), process(tup[1])), call_edges))
    return call_edges


def scoring_function(class1, rtntype1, name1, intype1, class2, rtntype2, name2, intype2):
    score = 0
    if class1 == class2:  # The two methods belong to the same package
        score += 10
    if rtntype1 == rtntype2:  # The two methods have a same return type
        score += 10
    if (name1 in name2) or (name2 in name1) or\
       (name1[0:2] == name2[0:2]) or (name1[0:2] == name2[0:2]):
        # The two methods start with a same prefix
        score += 10
    if intype1 == intype2:  # The two methods have a same input type
        score += 10
    return score > 20


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


def output_alledges(dataflow_dataframe, call_dataframe, sim_dataframe):
    dataflow_dataframe.to_csv("df.csv", mode='w+')
    call_dataframe.to_csv("callg.csv", mode='w+')
    sim_dataframe.to_csv("sim.csv", mode='w+')


def make_df_dataframe(dataflow_edges):
    """edges.csv에서의 data flow row를 만든다: tuple list를 dataframe으로 변환."""
    class1, rtntype1, name1, intype1, id1, class2, rtntype2, name2, intype2, id2 = [], [], [], [], [], [], [], [], [], []
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
    class1, rtntype1, name1, intype1, id1, class2, rtntype2, name2, intype2, id2 = [], [], [], [], [], [], [], [], [], []
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


def make_sim_dataframe(carPro):
    """edges.csv에서의 similarity row를 만든다: cartesian product 중 조건에 일치하는 것만 dataframe으로 변환."""
    mapfunc = lambda row: scoring_function(row['class1'], row['rtntype1'], row['name1'], row['intype1'],
                                           row['class2'], row['rtntype2'], row['name2'], row['intype2'])
    bool_df = carPro.apply(mapfunc, axis=1)
    carPro['leave'] = bool_df
    carPro = carPro[carPro.leave != False]
    carPro = carPro.drop(columns=['index1', 'index2', 'leave'])
    return carPro


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


def main():
    start = time.time()

    methodInfo1, methodInfo2, carPro = make_dataframes() # the main data we are manipulating
    json_obj_list = load_chain_json()
    dataflow_edges = detect_dataflow(json_obj_list)
    call_edges = make_calledges()

    dataflow_dataframe = make_df_dataframe(dataflow_edges)
    call_dataframe = make_call_dataframe(call_edges)
    sim_dataframe = make_sim_dataframe(carPro)

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
