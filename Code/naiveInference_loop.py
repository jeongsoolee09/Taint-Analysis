import pandas as pd
import time
import random
from re import match

methods = pd.read_csv("raw_data.csv", index_col=0)
edges = pd.read_csv("edges.csv", index_col=0)
edges.columns = pd.MultiIndex.from_product([['edge1', 'edge2'], methods.columns])
max_index_plus_one = methods.shape[0]

# Prior belief를 나타내는 자료구조 만들기
priors = pd.DataFrame(index=methods.index, columns=["src", "sin", "san", "non"])
priors = priors.fillna(0.25) # Flat priors!


def loop(times):
    for time in range(times):
        i = random.randint(0, max_index_plus_one-1)
        query = methods.loc[i][3]
        oracle_response = input("What label does <" + query + "> bear? [src/sin/san/non]: ")
        if oracle_response == 'src':
            bayesian_update(i, priors.loc[i], 'src')
        elif oracle_response == 'sin':
            bayesian_update(i, priors.loc[i], 'sin')
        elif oracle_response == 'san':
            bayesian_update(i, priors.loc[i], 'san')
        elif oracle_response == 'non':
            bayesian_update(i, priors.loc[i], 'non')
            

def bayesian_update(method_index, prior, oracle_response):
    if oracle_response == 'src':
        prior[0] = 1 * prior[0] / 0.25     # src
        prior[1] = 0 * prior[1] / 0.25     # sin
        prior[2] = 0 * prior[2] / 0.25     # san
        prior[3] = 0 * prior[3] / 0.25     # non
    elif oracle_response == 'sin':
        prior[0] = 0 * prior[0] / 0.25     # src
        prior[1] = 1 * prior[1] / 0.25     # sin
        prior[2] = 0 * prior[2] / 0.25     # san
        prior[3] = 0 * prior[3] / 0.25     # non
    elif oracle_response == 'san':
        prior[0] = 0 * prior[0] / 0.25     # src
        prior[1] = 0 * prior[1] / 0.25     # sin
        prior[2] = 1 * prior[2] / 0.25     # san
        prior[3] = 0 * prior[3] / 0.25     # non
    elif oracle_response == 'non':
        prior[0] = 0 * prior[0] / 0.25     # src
        prior[1] = 0 * prior[1] / 0.25     # sin
        prior[2] = 0 * prior[2] / 0.25     # san
        prior[3] = 1 * prior[3] / 0.25     # non
    belief_propagation(method_index)


def search_in_edge(node_index):
    # CASE 1: Match in LHS
    neighbors_l = edges.loc[methods["name"][node_index] == edges[('edge1', 'name')]]["edge2"]

    # CASE 2: Match in RHS
    neighbors_r = edges.loc[methods["name"][node_index] == edges[('edge2', 'name')]]["edge1"]

    neighbors = pd.concat([neighbors_l, neighbors_r])
    neighbors = neighbors.drop_duplicates()
    # # neighbors = neighbors.reset_index()
    # # neighbors = neighbors.drop("index", 1)
    return neighbors


def belief_propagation(node_index):
    """do it recursively: search for all associated tuples and call this function on those, too"""
    neighbors = search_in_edge(node_index)
    # print(neighbors)
    for neighbor in neighbors.itertuples(index=False):
        belief_propagation(int(neighbor[0]))


belief_propagation(130)
