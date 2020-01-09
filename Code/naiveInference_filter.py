import pandas as pd
import time
from re import match

start = time.time()

methodInfo1 = pd.read_csv("raw_data.csv", index_col=0)
methodInfo2 = pd.read_csv("raw_data.csv", index_col=0)

# print("")
# for i in range(5):
    # print(methodInfo1.loc[i])

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

edge1 = []
edge2 = []

print("starting bottleneck")
for row1 in methodInfo1.itertuples(index=False):
    for row2 in methodInfo2.itertuples(index=False):
        if scoring_function(row1, row2) >= 20:
            edge1.append(row1)
            edge2.append(row2)
print("completed bottleneck")

# print(len(list(methodInfo1['pkg'].unique()))) # outputs unique values of 'pkg' column

edges = pd.DataFrame({"edge1":edge1, "edge2":edge2})
edges.to_csv("edges.csv", mode='w')

print("elapsed time :", time.time() - start)
