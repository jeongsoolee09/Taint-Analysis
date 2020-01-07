# Naive Spec Inference.
# Graph Construction Criteria:
#     1. If a pair of methods belong to the same package: +10 to the pair
#     2. If a pair of methods start with a same prefix: +10 to the pair
#     3. If a pair of methods have a similar return type: +10 to the pair
#     4. If a pair of methods have a similar input type: +10 to the pair
# If the score is equal to 20, connect the pair with an edge.

import numpy as np
import time
import itertools
from re import match

start = time.time()

# Open and parse
fact = open("/home/jslee/taint/doop/cache/ccaa00b018a74b8a79db47d93aeaaff44fc921e1f6c9b35e0a2b642340a8a1c4/Method.facts", "r+")
factList = fact.readlines()
factList = list(map(lambda x: x.split("\t"), factList))
factList = list(map(lambda x: x[0], factList))
factList = np.asarray(factList)

regex = r'\((.*)\)'

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
    if '<init>' not in name and '<clinit>' not in name:
        return (pkg, rtntype, name, intype)

factList = np.array(list(map(process, factList)))
factList = factList[factList != np.array(None)] # wiping out None values
print(factList)

# Measuring similarity between methods
## 1. The pair of methods belong to the same package

# (pkg, rtntype, name, intype)

def scoring_function(info1, info2):
    score = 0
    if info1[0] == info2[0]: # The two methods belong to the same package
        score += 10
    if (info1[2] in info2[2]) or (info2[2] in info1[2]) or (info1[2][0:2] == info2[2][0:2]) or (info1[2][0:3] == info2[2][0:3]): # The two methods start with a same prefix
        score += 10
    if info1[1] == info2[1]: # The two methods have a similar return type 
        score += 10
    if info1[3] == info2[3]: # The two methods have a same input type
        score += 10
    return score

# def cartesian_product_transpose_pp(arrays):
#     la = len(arrays)
#     dtype = np.result_type(*arrays)
#     arr = np.empty((la, *map(len, arrays)), dtype=dtype)
#     idx = slice(None), *itertools.repeat(None, la)
#     for i, a in enumerate(arrays):
#         arr[i, ...] = a[idx[:la-i]]
#     return arr.reshape(la, -1).T

# carpro_factList = cartesian_product_transpose_pp([factList, factList])

for info1 in factList:
    for info2 in factList:
        if scoring_function(info1, info2) >= 20:
            edges.append((info1, info2))
edges = np.array(edges)

print("time :", time.time() - start)
