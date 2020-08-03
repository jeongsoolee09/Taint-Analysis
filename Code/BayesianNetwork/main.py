# Naive Spec Inference, augmented with real Bayesian Networks.
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

current_path = os.path.abspath("..")
methodfile = os.path.join(current_path, 'benchmarks',
                          'fabricated', 'Methods.txt')
callmethodfile = os.path.join(current_path, 'benchmarks',
                              'fabricated', 'Callgraph.txt')

setofallmethods = []


def flatten(ll):
    flat_list = []
    for sublist in ll:
        for item in sublist:
            flat_list.append(item)
    return flat_list


filtermethod = lambda string:\
    "__new" not in string and\
    "<init>" not in string and\
    "<clinit>" not in string and\
    "lambda" not in string and\
    "Lambda" not in string


def populate_sofallm():
    global setofallmethods
    methods = []
    callmethods = []
    with open(methodfile, "r+") as f:
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
    setofallmethods = list(map(lambda meth: process(meth), setofallmethods))


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



def write_to_csv():
    """Randomly select 100 methods from the set of all methods,
       or just use the set of all methods if possible"""
    writeList = []
    if len(setofallmethods) < 100:
        writeList = setofallmethods
    else:
        for i in random.sample(range(0, len(setofallmethods)), 100):
            writeList.append(setofallmethods[i])
    writeList = pd.DataFrame(writeList, columns=["pkg", "rtntype",
                                                 "name", "intype",
                                                 "id"], dtype="str")
    # embed the index into a separate column
    writeList = writeList.reset_index()
    writeList.to_csv("raw_data.csv", mode='w+')


def main():
    populate_sofallm()
    write_to_csv()


main()


print("elapsed time :", time.time() - start)
