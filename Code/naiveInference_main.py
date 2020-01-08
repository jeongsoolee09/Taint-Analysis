# Naive Spec Inference.
# Graph Construction Criteria:
#     1. If a pair of methods belong to the same package: +10 to the pair
#     2. If a pair of methods start with a same prefix: +10 to the pair
#     3. If a pair of methods have a similar return type: +10 to the pair
#     4. If a pair of methods have a similar input type: +10 to the pair
# If the score is equal to 20, connect the pair with an edge.

# Abandoning Numpy; transferring to Pandas

# import numpy as np
import pandas as pd
import time
import itertools
from re import match
import random

start = time.time()

regex = r'\((.*)\)'

# Parsing Function
def process(info):
    info = info.strip("<>")
    pkg = info.split(":")[0]
    rtntype = info.split(" ")[1]
    name = info.split(" ")[2]
    intype = match(regex, name)
    if intype is None:
        intype = 'void'
    else:
        intype = str(intype.group(1))
    return (pkg, rtntype, name, intype)

# Open and parse
fact = open("/home/jslee/taint/doop/cache/ccaa00b018a74b8a79db47d93aeaaff44fc921e1f6c9b35e0a2b642340a8a1c4/Method.facts", "r+")
factList = fact.readlines()
factList = list(map(lambda x: x.split("\t"), factList))
factList = list(map(lambda x: x[0], factList))
factList = list(map(process, factList))

writeList = []
for i in random.sample(range(0,len(factList)), 1000):
    writeList.append(factList[i])

writeList = pd.DataFrame(writeList, columns=["pkg", "rtntype", "name", "intype"], dtype="str")
# print("")
# print(factList.loc[0,"pkg"])
writeList.to_csv("raw_data.csv", mode='w')

# TODO: remove rows containing <init> and <clinit>

print("time :", time.time() - start)
