import pandas as pd
import time
from re import match

start = time.time()

methodInfo1 = pd.read_csv("raw_data.csv", index_col=0)
methodInfo2 = pd.read_csv("raw_data.csv", index_col=0)
methodInfo1 = methodInfo1.drop('id', axis=1)
methodInfo2 = methodInfo2.drop('id', axis=1)

def scoring_function(info1, info2):
    score = 0
    if info1[1] == info2[1]: # The two methods belong to the same package
        score += 10
    if (info1[3] in info2[3]) or (info2[3] in info1[3]) or (info1[3][0:2] == info2[3][0:2]) or (info1[3][0:2] == info2[3][0:2]): # The two methods start with a same prefix
        score += 10
    if info1[2] == info2[2]: # The two methods have a same return type 
        score += 10
    if info1[4] == info2[4]: # The two methods have a same input type
        score += 10
    return score

edge1 = []
edge2 = []

def desymmetrize(): # really really expensive. Replace it with an answer I got from SO!
    global edge1, edge2
    tmplst = list(zip(edge1,edge2))
    for (i,j) in tmplst:
        if (j,i) in tmplst:
            tmplst.remove((j,i))
    edge1 = list(list(zip(*tmplst))[0])
    edge2 = list(list(zip(*tmplst))[1])


print("starting bottleneck")
for row1 in methodInfo1.itertuples(index=False):
    for row2 in methodInfo2.itertuples(index=False):
        if scoring_function(row1, row2) >= 20:
            edge1.append(row1)
            edge2.append(row2)
print("completed bottleneck")

desymmetrize()

edge1 = pd.DataFrame(edge1, columns = methodInfo1.columns)
edge2 = pd.DataFrame(edge2, columns = methodInfo2.columns)
edges = pd.merge(edge1, edge2, left_index=True, right_index=True)
edges.columns = pd.MultiIndex.from_product([['edge1', 'edge2'], methodInfo1.columns])

edges.to_csv("edges.csv", mode='w')

print("elapsed time :", time.time() - start)
