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
    belief_propagation(method_index, oracle_response, 3)


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
    # cond1 = methods["index"][node_index] == edges[('edge1','index')]
    cond2 = methods["pkg"][node_index] == edges[('edge1','pkg')]
    cond3 = methods["rtntype"][node_index] == edges[('edge1','rtntype')]
    cond4 = methods["name"][node_index] == edges[('edge1','name')]
    cond5 = methods["intype"][node_index] == edges[('edge1','intype')]

    neighbors = edges[cond2 & cond3 & cond4 & cond5]["edge2"]
    neighbors = neighbors.drop_duplicates()
    return neighbors


def belief_propagation(node_index, oracle_response, depth):
    """do it recursively: search for all associated tuples and call this function on those, too"""
    if depth == 0:
        return
    neighbors = search_in_edge(node_index)
    for neighbor in neighbors.itertuples(index=False):
        if neighbor[0] == "index":   # empty methods, i.e. no further neighbors
            return
        bayesian_update_without_propagation(int(neighbor[0]), oracle_response)
        belief_propagation(int(neighbor[0]), oracle_response, depth-1)

loop(10)

def report_result():
    global priors
    one_src = priors['src'] == 1
    one_sin = priors['sin'] == 1
    one_san = priors['san'] == 1
    one_non = priors['non'] == 1
    ones = priors[one_src | one_sin | one_san | one_non]
    print("Touched {} methods".format(ones.shape[0]))
    print("Labels of the following methods are updated:")
    print(ones["id"])    
    priors.to_csv("result.csv", mode='w')
    print("report saved as result.csv")

report_result()
