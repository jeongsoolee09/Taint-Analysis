# 파라미터를 정당화하기 위한 그래프를 그리는 모듈. Not part of SpecHunter.

import networkx as nx
import os
import os.path
import random
from statistics import mean
from multiprocessing import Pool

from self_question_n_answer import single_loop
from split_underlying_graph import decycle
from make_BN import init_BN, exclude_rich, exclude_poor

DIRS = ["100-149", "150-199", "200-249", "250-299", "300-349", "350-399"]

def get_avg_times(directory):
    """주어진 디렉토리 안의 그래프들을 랜덤으로 10개 뽑아, 그 그래프들의 평균 문답 시간을 구한다."""
    graph_names = os.listdir(directory)
    sampled_graph_names = random.sample(graph_names, k=10)

    sampled_graph_names_and_graphs = list(map(lambda graph_name: (graph_name,
                                                                  nx.read_gpickle(directory+os.sep+graph_name)),
                                              sampled_graph_names))
    acc = []
    for name, graph in sampled_graph_names_and_graphs:
        decycle(graph)
        exclude_rich(graph)
        exclude_poor(graph)
        acc.append((name, graph))

    sampled_graph_names_and_graphs = acc

    sampled_graph_names_and_graphs_and_BNs = list(map(lambda tup: tup+(init_BN(tup[1]),),
                                                      sampled_graph_names_and_graphs))

    with Pool(20) as pool:
        loop_time_lists = pool.map(lambda tup: single_loop(*tup, loop_type="tactical"),
                                   sampled_graph_names_and_graphs_and_BNs)
    return list(map(lambda lst: mean(lst), loop_time_lists))


if __name__ == "__main__":
    get_avg_times("100-149")
