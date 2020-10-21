# 파라미터를 정당화하기 위한 그래프를 그리는 모듈. Not part of SpecHunter.

import networkx as nx
import os
import os.path
import random
import hashlib
import time
from statistics import mean
from multiprocessing import Pool

from self_question_n_answer import single_loop
from split_underlying_graph import decycle
from make_BN import init_BN, exclude_rich, exclude_poor
from community_detection import bisect

DIRS = ["100-149", "150-199", "200-249", "250-299", "300-349", "350-399"]


def collect_graph_by_mag_single(G):
    """split_large_graph의 수정 버전, 그래프를 잘라 나가면서 구간별로 해당되는 그래프를 collect"""
    worklist = [G]
    acc = []

    fifty_to_hundred = []
    hundred_to_hundredfifty = []
    hundredfifty_to_twohundred = []
    twohundred_to_twohundredfifty = []
    twohundredfifty_to_threehundred = []
    threehundred_to_threehundredfifty = []

    while worklist != []:
        print(list(map(lambda graph: len(graph.nodes), worklist)))
        target = worklist.pop()

        # match on target
        if 300 <= len(target.nodes) < 350:
            if target not in threehundred_to_threehundredfifty:
                threehundred_to_threehundredfifty.append(target)
        elif 250 <= len(target.nodes) < 300:
            if target not in twohundredfifty_to_threehundred:
                twohundredfifty_to_threehundred.append(target)
        elif 200 <= len(target.nodes) < 250:
            if target not in twohundred_to_twohundredfifty:
                twohundred_to_twohundredfifty.append(target)
        elif 150 <= len(target.nodes) < 200:
            if target not in hundredfifty_to_twohundred:
                hundredfifty_to_twohundred.append(target)
        elif 100 <= len(target.nodes) < 150:
            if target not in hundred_to_hundredfifty:
                hundred_to_hundredfifty.append(target)
        elif 50 <= len(target.nodes) < 100:
            if target not in fifty_to_hundred:
                fifty_to_hundred.append(target)

        if len(target.nodes) <= 49:
            acc.append(target)
        else:
            small1, small2 = bisect(target)

            # match on small1
            if 300 <= len(small1.nodes) < 350:
                if small1 not in threehundred_to_threehundredfifty:
                    threehundred_to_threehundredfifty.append(small1)
            elif 250 <= len(small1.nodes) < 300:
                if small1 not in twohundredfifty_to_threehundred:
                    twohundredfifty_to_threehundred.append(small1)
            elif 200 <= len(small1.nodes) < 250:
                if small1 not in twohundred_to_twohundredfifty:
                    twohundred_to_twohundredfifty.append(small1)
            elif 150 <= len(small1.nodes) < 200:
                if small1 not in hundredfifty_to_twohundred:
                    hundredfifty_to_twohundred.append(small1)
            elif 100 <= len(small1.nodes) < 150:
                if small1 not in hundred_to_hundredfifty:
                    hundred_to_hundredfifty.append(small1)
            elif 50 <= len(small1.nodes) < 100:
                if small1 not in fifty_to_hundred:
                    fifty_to_hundred.append(small1)

            # match on small2
            if 300 <= len(small2.nodes) < 350:
                if small2 not in threehundred_to_threehundredfifty:
                    threehundred_to_threehundredfifty.append(small2)
            elif 250 <= len(small2.nodes) < 300:
                if small2 not in twohundredfifty_to_threehundred:
                    twohundredfifty_to_threehundred.append(small2)
            elif 200 <= len(small2.nodes) < 250:
                if small2 not in twohundred_to_twohundredfifty:
                    twohundred_to_twohundredfifty.append(small2)
            elif 150 <= len(small2.nodes) < 200:
                if small2 not in hundredfifty_to_twohundred:
                    hundredfifty_to_twohundred.append(small2)
            elif 100 <= len(small2.nodes) < 150:
                if small2 not in hundred_to_hundredfifty:
                    hundred_to_hundredfifty.append(small2)
            elif 50 <= len(small2.nodes) < 100:
                if small2 not in fifty_to_hundred:
                    fifty_to_hundred.append(small2)

            if len(small1.nodes) == 0:
                acc.append(small2)
                continue
            elif len(small2.nodes) == 0:
                acc.append(small1)
                continue

            worklist.append(small1)
            worklist.append(small2)

    return (fifty_to_hundred,
            hundred_to_hundredfifty,
            hundredfifty_to_twohundred,
            twohundred_to_twohundredfifty,
            twohundredfifty_to_threehundred,
            threehundred_to_threehundredfifty)


def collect_graphs_by_mag(G):   # NOTE: *only use it on the REPL* with sagan-site as input G
    """위의 collect_graph_by_mag_single 함수를 여러 번 사용해 크기별 서브그래프들을 모음"""
    fifty_to_hundred = []
    hundred_to_hundredfifty = []
    hundredfifty_to_twohundred = []
    twohundred_to_twohundredfifty = []
    twohundredfifty_to_threehundred = []
    threehundred_to_threehundredfifty = []

    while len(threehundred_to_threehundredfifty) < 10:
        a, b, c, d, e, f = collect_graph_by_mag_single(G)
        fifty_to_hundred += a
        hundred_to_hundredfifty += b
        hundredfifty_to_twohundred += c
        twohundred_to_twohundredfifty += d
        twohundredfifty_to_threehundred += e
        threehundred_to_threehundredfifty += f

        for dirname, range_list in [("100-149", fifty_to_hundred),
                                    ("150-199", hundred_to_hundredfifty),
                                    ("200-249", hundredfifty_to_twohundred),
                                    ("250-299", twohundred_to_twohundredfifty),
                                    ("300-349", twohundredfifty_to_threehundred),
                                    ("350-399", threehundred_to_threehundredfifty)]:

            if not os.path.isdir(dirname):
                os.mkdir(dirname)
            for graph in range_list:
                hashobj = hashlib.sha256()
                now = str(time.time()).encode('UTF-8')
                hashobj.update(now)
                hashval = hashobj.hexdigest()
                nx.write_gpickle(graph, dirname+os.sep+hashval)


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
