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
    class_ = info.split(":")[0]
    rtntype = info.split(" ")[1]
    name = info.split(" ")[2]
    intype = regex.findall(name)[0]
    if intype == '':
        intype = 'void'
    name = name.split("(")[0]
    return (class_, rtntype, name, intype, info_)


# Open and parse
fact = open("/Users/jslee/Taint-Analysis/Code/benchmarks/realworld/Method.facts",
            "r+")
factList_original = fact.readlines()
factList = list(map(lambda x: x.split("\t"), factList_original))
factList = list(map(lambda x: x[0], factList))
factList = list(map(process, factList))
factList = list(filter(lambda tup: tup[2] != "<init>" and tup[2] != "<clinit>",
                       factList))

# Randomly select 1,000 methods from the set of all methods.
writeList = []
for i in random.sample(range(0, len(factList)), 75):
    writeList.append(factList[i])

writeList = pd.DataFrame(writeList, columns=["class", "rtntype", "name",
                                             "intype", "id"], dtype="str")
writeList = writeList.reset_index()  # embed the index into a separate column
writeList.to_csv("nodes.csv", mode='w')

idList = list(map(lambda x: x.split(">")[0]+'>', factList_original))
idList = pd.DataFrame(idList, columns=["id"])
idList.to_csv("id.csv", mode='w')

print("elapsed time :", time.time() - start)
