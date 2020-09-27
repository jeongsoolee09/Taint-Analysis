import json
import time
import numpy as np
import networkx as nx
import itertools as it

from pomegranate import *
from make_underlying_graph import find_root, find_edge_labels
from make_CPT import *


# Methods for BNs ====================================
# ====================================================

def create_roots_for_BN(G, BN):
    """identifies roots nodes from G and adds them to BN"""
    out = []
    for root in find_root(G):
        new_node = State(DiscreteDistribution({1.0: 0.25, 2.0: 0.25, 3.0: 0.25, 4.0: 0.25}), name=root)
        BN.add_state(new_node)
        out.append(new_node)
    return out


def create_internal_node_for_BN(graph_for_reference, node_name, BN, prev_states):
    """BN에 internal node를 만들어 추가한다."""
    labels = [1, 2, 3, 4]       # src, sin, san, non
    parents_and_edges = find_edge_labels(graph_for_reference, node_name)
    parents = list(map(lambda tup: tup[0], parents_and_edges)) 
    edges = list(map(lambda tup: tup[1], parents_and_edges))
    parent_dist = list(map(lambda state: state.distribution, prev_states))
    probs = create_CPT(edges).transpose().flatten()
    cond_prob_table_width = len(list(graph_for_reference.predecessors(node_name)))
    cond_prob_table_gen = it.repeat(labels, cond_prob_table_width+1)
    cond_prob_table = list(cond_prob_table_gen)
    cond_prob_table = it.product(*cond_prob_table)
    cond_prob_table = it.chain.from_iterable(cond_prob_table)
    cond_prob_table = np.fromiter(cond_prob_table, float).reshape(-1, cond_prob_table_width+1)
    cond_prob_table = np.c_[cond_prob_table, probs]
    cond_prob_table = cond_prob_table.tolist()
    cond_prob_table = ConditionalProbabilityTable(cond_prob_table, parent_dist)
    new_node = State(cond_prob_table, name=node_name)
    BN.add_state(new_node)
    return new_node


def find_BN_state(node_name, currently_defined_states):
    """node_name이 주어졌을 때, 지금까지 정의된 BN의 state들 중에서 이름이 node_name이랑 같은 노드를 내놓는다."""
    for state in currently_defined_states:
        if state.name == node_name:
            return state


def create_internal_nodes_for_BN(graph_for_reference, BN, currently_defined_states):
    """initialize the internal nodes using topological sort on graph_for_reference"""
    for node_name in list(nx.topological_sort(graph_for_reference)):
        if node_name in find_root(graph_for_reference):
            continue
        else:
            predecessor_names = list(graph_for_reference.predecessors(node_name))
            predecessor_nodes = list(map(lambda pred_name: find_BN_state(pred_name, currently_defined_states), predecessor_names))
            # print(list(map(lambda node: node.name, predecessor_nodes)))
            new_state = create_internal_node_for_BN(graph_for_reference, node_name, BN, predecessor_nodes)
            currently_defined_states.append(new_state)
    return currently_defined_states


def state_lookup(node_name, currently_defined_states):
    for state in currently_defined_states:
        if state.name == node_name:
            return state


def add_edge_to_BN(graph_for_reference, BN, currently_defined_states):
    """adds edges to BN"""
    for edge in graph_for_reference.edges:
        node1, node2 = edge
        state1 = state_lookup(node1, currently_defined_states)
        state2 = state_lookup(node2, currently_defined_states)
        BN.add_edge(state1, state2)


def init_BN(graph_for_reference):
    BN = BayesianNetwork("Interactive Inference of Taint Method Specifications")
    root_states = create_roots_for_BN(graph_for_reference, BN) 
    states = create_internal_nodes_for_BN(graph_for_reference, BN, root_states)
    add_edge_to_BN(graph_for_reference, BN, states)
    BN.bake()
    return BN


# Methods for Graphs =================================
# ====================================================

def exclude_rich(G):
    """incoming edge가 너무 많은 노드들을 그래프에서 삭제한다."""
    riches = []
    for node_name in G.nodes:
        if len(G.in_edges(nbunch=node_name)) > 6:
            riches.append(node_name)
    print("lost", len(riches), "rich nodes")
    for rich in riches:
        try:
            G.remove_node(rich)
        except:  # 이미 없넹
            pass
    return len(riches)


def exclude_poor(G):
    """고립된 노드들을 그래프에서 삭제한다."""
    while True:
        poors = []
        for node_name in G.nodes:
            if len(G.in_edges(nbunch=node_name)) == 0 and\
               len(G.out_edges(nbunch=node_name)) == 0:
                poors.append(node_name)
        print("lost", len(poors), "poor nodes")
        if poors == []:
            return
        for poor in poors:
            try:
                G.remove_node(poor)
            except:  # 이미 없넹
                pass
    return len(poors)


def main(graph_name):
    start = time.time()
    graph_for_reference = nx.read_gpickle(graph_name)
    print("graph has", len(graph_for_reference), "nodes")

    print("preprocessing...")
    
    num_of_riches = exclude_rich(graph_for_reference)
    num_of_poors = exclude_poor(graph_for_reference)

    print("initializing BN...")
    BN_for_inference = init_BN(graph_for_reference)
    print("BN initialized")

    nx.write_gpickle(graph_for_reference, graph_name)
    print("elapsed time:", time.time()-start)
    return BN_for_inference


if __name__ == "__main__":
    main()
