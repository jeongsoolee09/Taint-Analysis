import modin.pandas as pd
import time
import os
import json
from multiprocessing import Pool
from main import process
from itertools import repeat


def make_dataframes():
    methodInfo1 = pd.read_csv("raw_data.csv", index_col=0)
    methodInfo2 = pd.read_csv("raw_data.csv", index_col=0)

    methodInfo1 = methodInfo1.drop('id', axis=1)
    methodInfo2 = methodInfo2.drop('id', axis=1)

    # renaming columns for producing cartesian product by merging
    methodInfo1 = methodInfo1.rename(columns={'index':'index1', 'pkg':'pkg1',
                                              'rtntype':'rtntype1', 'name':'name1',
                                              'intype':'intype1'})
    methodInfo2 = methodInfo2.rename(columns={'index':'index2', 'pkg':'pkg2',
                                              'rtntype':'rtntype2', 'name':'name2',
                                              'intype':'intype2'})
    # Creating a key column for merging
    methodInfo1['key'] = 1
    methodInfo2['key'] = 1

    carPro = pd.merge(methodInfo1, methodInfo2, how='outer')
    carPro = carPro.drop('key', axis=1)

    # restoring column names
    methodInfo1 = methodInfo1.rename(columns={'index1':'index', 'pkg1':'pkg',
                                              'rtntype1':'rtntype', 'name1':'name',
                                              'intype1':'intype'})
    methodInfo2 = methodInfo2.rename(columns={'index2':'index', 'pkg2':'pkg',
                                              'rtntype2':'rtntype', 'name2':'name',
                                              'intype2':'intype'})
    return methodInfo1, methodInfo2, carPro


def filtermethod(string):
    return "__" not in string and\
        "<init>" not in string and\
        "<clinit>" not in string and\
        "lambda" not in string and\
        "Lambda" not in string


def load_chain_json():
    """Chain.json을 통째로 파싱해 파이썬 자료구조에 담는다. 결과값은 리스트이다."""
    path = os.path.abspath("..")
    path = os.path.join(path, "benchmarks", "realworld", "sagan", "Chain.json")
    with open(path, "r+") as chainjson:
        wrapped_chain_list = json.load(chainjson)
    return wrapped_chain_list


def make_calledges():
    path = os.path.abspath("..")
    path = os.path.join(path, "benchmarks", "realworld", "sagan", "Callgraph.txt")
    with open(path, "r+") as callgraphfile:
        lines = callgraphfile.readlines()
        lines = list(filter(filtermethod, lines))
        lines = list(map(lambda line: line.rstrip(), lines))
        lines = list(map(lambda line: line.split(" -> "), lines))
        call_edges = list(map(lambda lst: tuple(lst), lines))
        call_edges = list(map(lambda tup: (process(tup[0]), process(tup[1])), call_edges))
    return call_edges


def scoring_function(pkg1, rtntype1, name1, intype1, pkg2, rtntype2, name2, intype2):
    score = 0
    if pkg1 == pkg2:  # The two methods belong to the same package
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


def output_dfedges(dataflow_edges):
    with open("df.txt", "w+") as df:
        for (dfsend, dfrcv) in dataflow_edges:
            df.write(dfsend + ", " + dfrcv + "\n")


def output_calledges(call_edges):
    with open("callg.txt", "w+") as call:
        for (caller, callee) in call_edges:
            call.write(caller + ", " + callee + "\n")


def output_alledges(dataflow_edges, call_edges):
    output_dfedges(dataflow_edges)
    output_calledges(call_edges)


def make_df_dataframe(dataflow_edges):
    """edges.csv에서의 data flow row를 만든다: tuple list를 dataframe으로 변환."""
    pkg1, rtntype1, name1, intype1, pkg2, rtntype2, name2, intype2 = tuple(repeat([], 8))
    for df_edge in dataflow_edges:
       parent = df_edge[0]
       child = df_edge[1]
       pkg1.append(parent[0])
       rtntype1.append(parent[1])
       name1.append(parent[2])
       intype1.append(parent[3])
       pkg2.append(parent[0])
       rtntype2.append(parent[1])
       name2.append(parent[2])
       intype2.append(parent[3])
    return pd.DataFrame({'pkg1': pkg1, 'rtntype1': rtntype1, 'name1': name1, 'intype1': intype1,
                         'pkg2': pkg2, 'rtntype2': rtntype2, 'name2': name2, 'intype2': intype2})
       

def make_call_dataframe(call_edges):
    """edges.csv에서의 call row를 만든다: tuple list를 dataframe으로 변환."""
    pkg1, rtntype1, name1, intype1, pkg2, rtntype2, name2, intype2 = tuple(repeat([], 8))
    for call_edge in call_edges:
       parent = call_edge[0]
       child = call_edge[1]
       pkg1.append(parent[0])
       rtntype1.append(parent[1])
       name1.append(parent[2])
       intype1.append(parent[3])
       pkg2.append(parent[0])
       rtntype2.append(parent[1])
       name2.append(parent[2])
       intype2.append(parent[3])
    return pd.DataFrame({'pkg1': pkg1, 'rtntype1': rtntype1, 'name1': name1, 'intype1': intype1,
                         'pkg2': pkg2, 'rtntype2': rtntype2, 'name2': name2, 'intype2': intype2})


def make_sim_dataframe(carPro):
    """edges.csv에서의 similarity row를 만든다: cartesian product 중 조건에 일치하는 것만 dataframe으로 변환."""
    mapfunc = lambda row: scoring_function(row['pkg1'], row['rtntype1'], row['name1'], row['intype1'],
                                           row['pkg2'], row['rtntype2'], row['name2'], row['intype2'])
    bool_df = carPro.apply(mapfunc, axis=1)
    carPro['leave'] = bool_df
    carPro = carPro[carPro.leave != False]
    return carPro


def merge_dataframes(df_dataframe, call_dataframe, sim_dataframe):
    """df, call, sim dataframe 세 개를 하나로 합친다."""
    return df_dataframe.append(call_dataframe).append(sim_dataframe)


def multiindex_carPro(carPro):
    """carPro dataframe이 주어졌을 때, 그 dataframe을 multiindex로 바꾼다."""
    edge1_high = list(repeat('edge1', 5))
    edge2_high = list(repeat('edge2', 5))
    high_edges = edge1_high + edge2_high
    edge1_index = list(carPro.columns)[0:5]
    edge1_index = list(map(lambda index: index[0:len(index)-1], edge1_index))
    edge2_index = list(carPro.columns)[5:10]
    edge2_index = list(map(lambda index: index[0:len(index)-1], edge2_index))
    low_edges = edge1_index + edge2_index
    tuples = list(zip(high_edges, low_edges))
    index = pd.MultiIndex.from_tuples(tuples)
    carPro.columns = index
    return carPro
    

def no_symmetric(dataframe):
    dataframe['temp'] = dataframe.index * 2
    dataframe2 = dataframe.iloc[:, [5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 10]]
    dataframe2.columns = dataframe.columns
    dataframe2['temp'] = dataframe2.index * 2 + 1
    out = pd.concat([dataframe, dataframe2])
    out = out.sort_values(by='temp')
    out = out.set_index('temp')
    out = out.drop_duplicates()
    out = out[out.index % 2 == 0]
    out = out.reset_index()[['edge1', 'edge2']]
    return out


def no_symmetric_carPro(carPro):
    carPro['temp'] = carPro.index * 2
    carPro2 = carPro.iloc[:, [5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 10]]
    carPro2.columns = carPro.columns
    carPro2['temp'] = carPro2.index * 2 + 1
    out = pd.concat([carPro, carPro2])

    # 밑에부터가 문제
    out = out.sort_values(by='temp')
    out = out.set_index('temp')
    out = out.drop_duplicates()
    out = out[out.index % 2 == 0]
    out = out.reset_index()[['edge1', 'edge2']]
    return out


def no_reflexive(dataframe):
    cond1 = dataframe[('edge1', 'index')] != dataframe[('edge2', 'index')]
    cond2 = dataframe[('edge1', 'pkg')] != dataframe[('edge2', 'pkg')]
    cond3 = dataframe[('edge1', 'rtntype')] != dataframe[('edge2', 'rtntype')]
    cond4 = dataframe[('edge1', 'name')] != dataframe[('edge2', 'name')]
    cond5 = dataframe[('edge1', 'intype')] != dataframe[('edge2', 'intype')]
    return dataframe[cond1 | cond2 | cond3 | cond4 | cond5]


def test_reflexive(dataframe):
    reflex1 = dataframe[('edge1', 'index')] == dataframe[('edge2', 'index')]
    reflex2 = dataframe[('edge1', 'pkg')] == dataframe[('edge2', 'pkg')]
    reflex3 = dataframe[('edge1', 'rtntype')] == dataframe[('edge2', 'rtntype')]
    reflex4 = dataframe[('edge1', 'name')] == dataframe[('edge2', 'name')]
    reflex5 = dataframe[('edge1', 'intype')] == dataframe[('edge2', 'intype')]
    return dataframe[reflex1 & reflex2 & reflex3 & reflex4 & reflex5]


def main():
    methodInfo1, methodInfo2, carPro = make_dataframes() # the main data we are manipulating
    json_obj_list = load_chain_json()
    dataflow_edges = detect_dataflow(json_obj_list)
    call_edges = make_calledges()
    dataflow_dataframe = make_df_dataframe(dataflow_edges)
    call_dataframe = make_call_dataframe(call_edges)
    sim_dataframe = make_sim_dataframe(carPro)
    edges_dataframe = merge_dataframes(dataflow_dataframe, call_dataframe, sim_dataframe)

    output_alledges(dataflow_edges, call_edges)

    make_multicolumn(methodInfo1, methodInfo2, edge1, edge2)
    edges_new = no_reflexive(no_symmetric(edges))
    edges_new.to_csv("edges.csv", mode='w')
    print("elapsed time: ", time.time()-start)

