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

setofallmethods = []


def populate_sofallm():
    global setofallmethods
    with open(methodfile, "r+") as f:
        for line in f.readlines():
            setofallmethods.append(line.rstrip())
    setofallmethods = list(filter(lambda string: "<init>" not in string and
                                  "<clinit>" not in string, setofallmethods))
    setofallmethods = list(map(lambda meth: process(meth), setofallmethods))


def process(info):
    pkg = info.split('.')[0].split(' ')[1]
    rtntype = info.split('.')[0].split(' ')[0]
    name_and_type = info.split('.')[1]
    name = name_and_type.split('(')[0]
    intype = regex.findall(name_and_type)[0]
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
    writeList = writeList.reset_index()  # embed the index into a separate column
    writeList.to_csv("raw_data.csv", mode='w+')


def main():
    populate_sofallm()
    write_to_csv()


main()


print("elapsed time :", time.time() - start)
