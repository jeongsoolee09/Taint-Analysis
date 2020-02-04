import pandas as pd
import time
import random

methods = pd.read_csv("raw_data.csv", index_col=0)
ids = methods["id"]
methods = methods.drop('id', axis=1) # unleash me when you're done!
edges = pd.read_csv("edges.csv", index_col=0)
edges.columns = pd.MultiIndex.from_product([['edge1', 'edge2'], methods.columns])
max_index_plus_one = methods.shape[0]

# Prior beliefs
priors = pd.DataFrame(index=methods.index, columns=["src", "sin", "san", "non"])
priors = priors.fillna(0.25) # Flat priors!
priors = pd.merge(priors, ids, left_index=True, right_index=True)


def loop(times):
    for time in range(times):
        i = random.randint(0, max_index_plus_one-1)
        query = methods.loc[i][3]
        oracle_response = input("What label does <" + query + "> bear? [src/sin/san/non]: ")
        if oracle_response == 'src':
            bayesian_update(i, 'src')
        elif oracle_response == 'sin':
            bayesian_update(i, 'sin')
        elif oracle_response == 'san':
            bayesian_update(i, 'san')
        elif oracle_response == 'non':
            bayesian_update(i, 'non')
            

def bayesian_update(method_index, oracle_response):
    global priors
    if oracle_response == 'src':
        priors.at[method_index, 'src'] = 1 * priors.loc[method_index, 'src'] / 0.25     # src
        priors.at[method_index, 'sin'] = 0 * priors.loc[method_index, 'sin'] / 0.25     # sin
        priors.at[method_index, 'san'] = 0 * priors.loc[method_index, 'san'] / 0.25     # san
        priors.at[method_index, 'non'] = 0 * priors.loc[method_index, 'non'] / 0.25     # non
    elif oracle_response == 'sin':
        priors.at[method_index, 'src'] = 0 * priors.loc[method_index, 'src'] / 0.25     # src
        priors.at[method_index, 'sin'] = 1 * priors.loc[method_index, 'sin'] / 0.25     # sin
        priors.at[method_index, 'san'] = 0 * priors.loc[method_index, 'san'] / 0.25     # san
        priors.at[method_index, 'non'] = 0 * priors.loc[method_index, 'non'] / 0.25     # non
    elif oracle_response == 'san':
        priors.at[method_index, 'src'] = 0 * priors.loc[method_index, 'src'] / 0.25     # src
        priors.at[method_index, 'sin'] = 0 * priors.loc[method_index, 'sin'] / 0.25     # sin
        priors.at[method_index, 'san'] = 1 * priors.loc[method_index, 'san'] / 0.25     # san
        priors.at[method_index, 'non'] = 0 * priors.loc[method_index, 'non'] / 0.25     # non
    elif oracle_response == 'non':
        priors.at[method_index, 'src'] = 0 * priors.loc[method_index, 'src'] / 0.25     # src
        priors.at[method_index, 'sin'] = 0 * priors.loc[method_index, 'sin'] / 0.25     # sin
        priors.at[method_index, 'san'] = 0 * priors.loc[method_index, 'san'] / 0.25     # san
        priors.at[method_index, 'non'] = 1 * priors.loc[method_index, 'non'] / 0.25     # non
    belief_propagation(method_index, oracle_response, 2)    # propagation depth = 2

def bayesian_update_without_propagation(method_index, oracle_response):
    global priors
    if oracle_response == 'src' and priors.loc[method_index, 'src']<=1:
        priors.at[method_index, 'src'] = 1 * priors.loc[method_index, 'src'] / 0.25     # src
        priors.at[method_index, 'sin'] = 0 * priors.loc[method_index, 'sin'] / 0.25     # sin
        priors.at[method_index, 'san'] = 0 * priors.loc[method_index, 'san'] / 0.25     # san
        priors.at[method_index, 'non'] = 0 * priors.loc[method_index, 'non'] / 0.25     # non
    elif oracle_response == 'sin' and priors.loc[method_index, 'sin']<=1:
        priors.at[method_index, 'src'] = 0 * priors.loc[method_index, 'src'] / 0.25     # src
        priors.at[method_index, 'sin'] = 1 * priors.loc[method_index, 'sin'] / 0.25     # sin
        priors.at[method_index, 'san'] = 0 * priors.loc[method_index, 'san'] / 0.25     # san
        priors.at[method_index, 'non'] = 0 * priors.loc[method_index, 'non'] / 0.25     # non
    elif oracle_response == 'san' and priors.loc[method_index, 'san']<=1:
        priors.at[method_index, 'src'] = 0 * priors.loc[method_index, 'src'] / 0.25     # src
        priors.at[method_index, 'sin'] = 0 * priors.loc[method_index, 'sin'] / 0.25     # sin
        priors.at[method_index, 'san'] = 1 * priors.loc[method_index, 'san'] / 0.25     # san
        priors.at[method_index, 'non'] = 0 * priors.loc[method_index, 'non'] / 0.25     # non
    elif oracle_response == 'non' and priors.loc[method_index, 'non']<=1:
        priors.at[method_index, 'src'] = 0 * priors.loc[method_index, 'src'] / 0.25     # src
        priors.at[method_index, 'sin'] = 0 * priors.loc[method_index, 'sin'] / 0.25     # sin
        priors.at[method_index, 'san'] = 0 * priors.loc[method_index, 'san'] / 0.25     # san
        priors.at[method_index, 'non'] = 1 * priors.loc[method_index, 'non'] / 0.25     # non


def search_in_edge(node_index):
    """finds an immediate neighbor on the graph structure"""
    # CASE 1: Match in LHS
    neighbors_l = edges.loc[methods["name"][node_index] == edges[('edge1', 'name')]]["edge2"]

    # CASE 2: Match in RHS
    neighbors_r = edges.loc[methods["name"][node_index] == edges[('edge2', 'name')]]["edge1"]

    neighbors = pd.concat([neighbors_l, neighbors_r])
    neighbors = neighbors.drop_duplicates()
    return neighbors


def belief_propagation(node_index, oracle_response, times):
    """do it recursively: search for all associated tuples and call this function on those, too"""
    print(node_index)
    if times == 0:
        return
    neighbors = search_in_edge(node_index)
    for neighbor in neighbors.itertuples(index=False):
        if neighbor[0] == "index":   # empty dataframe, i.e. no further neighbors
            return
        bayesian_update_without_propagation(int(neighbor[0]), oracle_response)
        belief_propagation(int(neighbor[0]), oracle_response, times)

loop(10)

def report_result():
    global priors
    condition_src = priors['src'] == 1
    condition_sin = priors['sin'] == 1
    condition_san = priors['san'] == 1
    condition_non = priors['non'] == 1
    nonzeros = priors[condition_src | condition_sin | condition_san | condition_non]
    print("Touched {} methods".format(nonzeros.shape[0]))
    print("Labels of the following methods are updated:")
    print(nonzeros["id"])    
    priors.to_csv("result.csv", mode='w')
    print("report saved as result.csv")

report_result()
