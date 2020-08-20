# Spec Inference with real Bayesian Networks.
# Graph Construction Criteria:
#     1. If a pair of methods belong to the same package: +10 to the pair
#     2. If a pair of methods start with a same prefix: +10 to the pair
#     3. If a pair of methods have a similar return type: +10 to the pair
#     4. If a pair of methods have a similar input type: +10 to the pair
# If the score is equal to 20, connect the pair with an edge.

import pandas as pd
import time
import re
import random
import os

start = time.time()

regex = r'\((.*)\)'
regex = re.compile(regex)

# let's read the files created by static analysis
upper_path = os.path.abspath("..")
methodfile = os.path.join(upper_path, 'benchmarks',
                          'realworld', 'sagan', 'Methods.txt')
callmethodfile = os.path.join(upper_path, 'benchmarks',
                              'realworld', 'sagan', 'Callgraph.txt')
skipfuncfile = os.path.join(upper_path, 'benchmarks',
                              'realworld', 'sagan', 'skip_func.txt')

def flatten(ll):
    flat_list = []
    for sublist in ll:
        for item in sublist:
            flat_list.append(item)
    return flat_list


filtermethod = lambda string:\
    "__" not in string and\
    "<init>" not in string and\
    "<clinit>" not in string and\
    "lambda" not in string and\
    "Lambda" not in string


def process(info):
    space_index = info.index(' ')
    split_on_open_paren = info.split('(')
    last_dot_index = split_on_open_paren[0].rindex('.')
    open_paren_index = info.index('(')
    rtntype = info[:space_index]
    pkg = info[space_index+1:last_dot_index]
    name = info[last_dot_index+1:open_paren_index]
    intype = regex.findall(info)[0]
    if intype == '':
        intype = 'void'
    return (pkg, rtntype, name, intype, info)


def populate_sofallm():
    setofallmethods = []
    methods = []
    callmethods = []
    with open(methodfile, "r+") as f:
        lines = f.readlines()
        for line in f.readlines():
            methods.append(line.rstrip())
    methods = list(filter(filtermethod, methods))
    methods = set(methods)
    with open(callmethodfile, "r+") as g:
        for line in g.readlines():
            callmethods.append(line.rstrip())
    callmethods = list(filter(filtermethod, callmethods))
    callmethods = list(map(lambda line: line.rstrip(), callmethods))
    callmethods = list(map(lambda line: line.split(" -> "), callmethods))
    callmethods = set(flatten(callmethods))
    setofallmethods = list(methods.union(callmethods))
    setofallmethods = list(filter(lambda meth: ' ' in meth, setofallmethods))
    # process에서 모든 heavy lifting 담당
    setofallmethods = list(map(process, setofallmethods))
    return setofallmethods


def populate_skipmethods():
    skipmethods = []
    with open(skipfuncfile, "r+") as f:
        lines = f.readlines()
        for line in lines:
            skipmethods.append(line.rstrip())
    skipmethods = list(filter(filtermethod, skipmethods))
    skipmethods = list(map(process, skipmethods))
    return skipmethods


setofallmethods = populate_sofallm()
skipmethods = populate_skipmethods()


def write_to_csv():
    """Randomly select 100 methods from the set of all methods,
       or just use the set of all methods if possible and save them to csv"""
    write_list = []
    if len(setofallmethods) < 100:
        write_list = setofallmethods
    else:
        for i in random.sample(range(0, len(setofallmethods)), 100):
            write_list.append(setofallmethods[i])
    write_list = pd.DataFrame(write_list, columns=["pkg", "rtntype",
                                                   "name", "intype", "id"],
                              dtype="str")
    # embed the index into a separate column
    write_list = write_list.reset_index()
    write_list.to_csv("raw_data.csv", mode='w+')


def skip_func_to_csv():
    """skip_func.txt를 읽고 필터링한 결과를 csv로 저장"""
    write_list = skipmethods
    write_list = pd.DataFrame(write_list, columns=["pkg", "rtntype",
                                                   "name", "intype", "id"],
                              dtype="str")
    write_list = write_list.reset_index()
    write_list.to_csv("skip_func.csv", mode='w+')


def main():
    populate_sofallm()
    write_to_csv()
    skip_func_to_csv()


main()


print("elapsed time :", time.time() - start)
