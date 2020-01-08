import pandas as pd
import time
from re import match

methodInfo1 = pd.read_csv("raw_data.csv", index_col=0, chunksize=1000)
methodInfo2 = pd.read_csv("raw_data.csv", index_col=0, chunksize=1000)

# print("")
# for i in range(5):
#     print(methodInfo.loc[i])
# print(methodInfo1)
# print(methodInfo2)

def scoring_function(info1, info2):
    score = 0
    if info1[0] == info2[0]: # The two methods belong to the same package
        score += 10
    if (info1[2] in info2[2]) or (info2[2] in info1[2]) or (info1[2][0:2] == info2[2][0:2]) or (info1[2][0:3] == info2[2][0:3]): # The two methods start with a same prefix
        score += 1
        0
    if info1[1] == info2[1]: # The two methods have a similar return type 
        score += 10
    if info1[3] == info2[3]: # The two methods have a same input type
        score += 10
    return score

