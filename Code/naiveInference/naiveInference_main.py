# Naive Spec Inference.
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

start = time.time()

regex = r'\((.*)\)'
regex = re.compile(regex)

# Parsing Function
def process(info):
    info_ = info
    info = info.strip("<>")
    pkg = info.split(":")[0]
    rtntype = info.split(" ")[1]
    name = info.split(" ")[2]
    intype = regex.findall(name)[0]
    if intype == '':
        intype = 'void'
    name = name.split("(")[0]
    return (pkg, rtntype, name, intype, info_)

# Open and parse
fact = open("/home/jslee/taint/doop/cache/ccaa00b018a74b8a79db47d93aeaaff44fc921e1f6c9b35e0a2b642340a8a1c4/Method.facts", "r+")
factList_original = fact.readlines()
factList = list(map(lambda x: x.split("\t"), factList_original))
factList = list(map(lambda x: x[0], factList))
factList = list(map(process, factList))
factList = list(filter(lambda tup: tup[2] != "<init>" and tup[2] != "<clinit>", factList))

# Randomly select 1,000 methods from the set of all methods.
writeList = []
for i in random.sample(range(0,len(factList)), 1000):
    writeList.append(factList[i])

writeList = pd.DataFrame(writeList, columns=["pkg", "rtntype", "name", "intype", "id"], dtype="str")
writeList = writeList.reset_index() # embed the index into a separate column
writeList.to_csv("raw_data.csv", mode='w')

idList = list(map(lambda x: x.split(">")[0]+'>', factList_original))
idList = pd.DataFrame(idList, columns=["id"])
idList.to_csv("id.csv", mode='w')

print("elapsed time :", time.time() - start)
