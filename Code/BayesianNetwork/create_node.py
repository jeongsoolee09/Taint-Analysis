# Spec Inference with real Bayesian Networks.
# Graph Construction Criteria:
#     1. If a pair of methods belong to the same package: +10 to the pair
#     2. If a pair of methods start with a same prefix: +10 to the pair
#     3. If a pair of methods have a similar return type: +10 to the pair
#     4. If a pair of methods have a similar input type: +10 to the pair
# If the score is more than 20, connect the pair with an edge.

import pandas as pd
import time
import re
import os.path
import glob


regex = r'\((.*)\)'
regex = re.compile(regex)
    

def flatten(ll):
    flat_list = []
    for sublist in ll:
        for item in sublist:
            flat_list.append(item)
    return flat_list


def filtermethod(string):
    return "$" not in string and\
           "__" not in string and\
           "<init>" not in string and\
           "<clinit>" not in string and\
           "lambda" not in string and\
           "Lambda" not in string


def process(method_id):
    """splits a method id into (classname, rtntype, methodname, intype, id)"""
    space_index = method_id.index(' ')
    split_on_open_paren = method_id.split('(')
    last_dot_index = split_on_open_paren[0].rindex('.')
    open_paren_index = method_id.index('(')
    rtntype = method_id[:space_index]
    class_ = method_id[space_index+1:last_dot_index]
    name = method_id[last_dot_index+1:open_paren_index]
    intype = regex.findall(method_id)[0]
    if intype == '':
        intype = 'void'
    return (class_, rtntype, name, intype, method_id)


def populate_sofallm(methodfile, callgraphfile):
    setofallmethods = []
    methods = []
    callmethods = []
    with open(methodfile, "r+") as f:
        lines = f.readlines()
        for line in f.readlines():
            methods.append(line.rstrip())
    methods = list(filter(filtermethod, methods))
    methods = set(methods)
    with open(callgraphfile, "r+") as g:
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


def write_to_csv(setofallmethods):
    write_list = setofallmethods
    write_list = pd.DataFrame(write_list, columns=["pkg", "rtntype",
                                                   "name", "intype", "id"],
                              dtype="str")
    # embed the index into a separate column
    write_list = write_list.reset_index()
    write_list.to_csv("nodes.csv", mode='w+')


def main():
    start = time.time()

    # let's read the files created by static analysis
    upper_path = os.path.abspath("..")
    methodfile = os.path.join(upper_path, 'benchmarks',
                              'realworld', 'sagan', 'Methods.txt')
    callgraphfile = os.path.join(upper_path, 'benchmarks',
                                 'realworld', 'sagan', 'Callgraph.txt')
    skipfuncfile = os.path.join(upper_path, 'benchmarks',
                                'realworld', 'sagan', 'skip_func.txt')

    setofallmethods = populate_sofallm(methodfile, callgraphfile)
    write_to_csv(setofallmethods)

    print("elapsed time :", time.time() - start)


if __name__ == "__main__":
    main()
