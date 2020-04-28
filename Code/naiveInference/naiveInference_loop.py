import random
import pandas as pd
import matplotlib.pyplot as plt
import networkx as nx
import os

current_path = os.path.abspath('')
# raw_data = os.path.join(current_path, 'naiveInference', 'raw_data.csv')
# edges = os.path.join(current_path, 'naiveInference', 'edges.csv')
raw_data = os.path.join(current_path, 'raw_data.csv')
edges = os.path.join(current_path, 'edges.csv')
methods = pd.read_csv(raw_data, index_col=0)
ids = methods["id"]
methods = methods.drop('id', axis=1)
edges = pd.read_csv(edges, index_col=0)
edges.columns = pd.MultiIndex.from_product([['edge1', 'edge2'],
                                            methods.columns])


max_index_plus_one = methods.shape[0]

# Prior beliefs
priors = pd.DataFrame(index=methods.index, columns=["src", "sin",
                                                    "san", "non"])
priors = priors.fillna(0.25)  # Flat priors!
priors = pd.merge(priors, ids, left_index=True, right_index=True)


def interact():
    i = random.randint(0, max_index_plus_one-1)
    query = methods.loc[i][3]
    oracle_response = input("What label does <" + query +
                            "> bear? [src/sin/san/non]: ")
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
    if oracle_response == 'src' and priors.loc[method_index, 'src'] <= 1:
        priors.at[method_index, 'src'] = 1 * priors.loc[method_index, 'src'] / 0.25     # src
        priors.at[method_index, 'sin'] = 0 * priors.loc[method_index, 'sin'] / 0.25     # sin
        priors.at[method_index, 'san'] = 0 * priors.loc[method_index, 'san'] / 0.25     # san
        priors.at[method_index, 'non'] = 0 * priors.loc[method_index, 'non'] / 0.25     # non
    elif oracle_response == 'sin' and priors.loc[method_index, 'sin'] <= 1:
        priors.at[method_index, 'src'] = 0 * priors.loc[method_index, 'src'] / 0.25     # src
        priors.at[method_index, 'sin'] = 1 * priors.loc[method_index, 'sin'] / 0.25     # sin
        priors.at[method_index, 'san'] = 0 * priors.loc[method_index, 'san'] / 0.25     # san
        priors.at[method_index, 'non'] = 0 * priors.loc[method_index, 'non'] / 0.25     # non
    elif oracle_response == 'san' and priors.loc[method_index, 'san'] <= 1:
        priors.at[method_index, 'src'] = 0 * priors.loc[method_index, 'src'] / 0.25     # src
        priors.at[method_index, 'sin'] = 0 * priors.loc[method_index, 'sin'] / 0.25     # sin
        priors.at[method_index, 'san'] = 1 * priors.loc[method_index, 'san'] / 0.25     # san
        priors.at[method_index, 'non'] = 0 * priors.loc[method_index, 'non'] / 0.25     # non
    elif oracle_response == 'non' and priors.loc[method_index, 'non'] <= 1:
        priors.at[method_index, 'src'] = 0 * priors.loc[method_index, 'src'] / 0.25     # src
        priors.at[method_index, 'sin'] = 0 * priors.loc[method_index, 'sin'] / 0.25     # sin
        priors.at[method_index, 'san'] = 0 * priors.loc[method_index, 'san'] / 0.25     # san
        priors.at[method_index, 'non'] = 1 * priors.loc[method_index, 'non'] / 0.25     # non


def search_in_edge(node_index):
    """finds an immediate neighbor on the graph structure"""
    # cond1 = methods["index"][node_index] == edges[('edge1','index')]
    cond2 = methods["pkg"][node_index] == edges[('edge1', 'pkg')]
    cond3 = methods["rtntype"][node_index] == edges[('edge1', 'rtntype')]
    cond4 = methods["name"][node_index] == edges[('edge1', 'name')]
    cond5 = methods["intype"][node_index] == edges[('edge1', 'intype')]

    neighbors = edges[cond2 & cond3 & cond4 & cond5]["edge2"]
    neighbors = neighbors.drop_duplicates()
    return neighbors


def belief_propagation(node_index, oracle_response, depth):
    """do it recursively: search for all associated tuples
    and call this function on those, too"""
    if depth == 0:
        return
    neighbors = search_in_edge(node_index)
    for neighbor in neighbors.itertuples(index=False):
        if neighbor[0] == "index":   # empty methods, i.e. no further neighbors
            return
        bayesian_update_without_propagation(int(neighbor[0]), oracle_response)
        belief_propagation(int(neighbor[0]), oracle_response, depth-1)


def loop(times):
    '''perform an interaction, color the node with updated beliefs,
    and show the graph'''
    for _ in range(times):
        interact()
        update_node_color()
        show_graph()


labeldict = {1: "src", 2: "sin", 3: "san", 4: "non"}
colordict = {"src": "red", "sin": "orange", "san": "yellow", "non": "green"}


def update_node_color():
    global vis_color_map
    for probs in priors.itertuples():
        index = probs[0]
        nodelist_index = find_in_nodelist(str(index))
        if probs[1] == probs[2] == probs[3] == probs[4]:
            pass  # unscorable
        else:
            label = labeldict[probs.index(max(probs[1], probs[2],
                                              probs[3], probs[4]))]
            color = colordict[label]
            print(nodelist_index)
            vis_color_map[nodelist_index] = color


def show_graph():
    """clear the plot and redraw the network again."""
    plt.clf()
    nx.draw(graph_for_vis, node_color=vis_color_map, pos=nx.kamada_kawai_layout(graph_for_vis),
            with_labels=True, node_size=100)
    plt.show()


def init_graph():
    """Initialize a (directed acyclic) graph for visualization."""
    G = nx.DiGraph()
    build_graph(G)
    return G


def build_graph(G):
    add_node(G)
    add_edge(G)


# not for demo purposes
def add_node(G):
    for method in methods.itertuples():
        index = method[0]
        name = method[4]
        G.add_node((str(index), name))


# use this only for demo purposes
def add_edge(G):
    """adds edges to reference graph G.
    V is a subset of index * name"""
    for edge in edges.itertuples():
        index1 = edge[1]
        name1 = edge[4]
        index2 = edge[6]
        name2 = edge[9]
        first = (index1, name1)
        second = (index2, name2)
        G.add_edge(first, second)


graph_for_vis = init_graph()
vis_color_map = ["blue"] * graph_for_vis.number_of_nodes()

# only for demo purposes
nodelist = list(set(list(graph_for_vis.nodes())))


def find_in_nodelist(index):
    for (index_, meth) in nodelist:
        if index == index_:
            return nodelist.index((index_, meth))


def report_result():
    one_src = priors['src'] == 1
    one_sin = priors['sin'] == 1
    one_san = priors['san'] == 1
    one_non = priors['non'] == 1
    ones = priors[one_src | one_sin | one_san | one_non]
    print("\nTouched {} methods".format(ones.shape[0]))
    print("Labels of the following methods are updated:")
    print(ones["id"])
    priors.to_csv("result.csv", mode='w')
    print("\nreport saved as result.csv")


loop(10)
report_result()
