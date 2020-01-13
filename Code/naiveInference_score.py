import pandas as pd
import numpy as np
import time
import random
from re import match


# 채점을 자동으로 하기 위한 방법:
# 1. prior dataframe을 불러온다.
# 2. for_scoring dataframe을 만든다. Column = ['name', 'estimated label'].
# 3. 그리고 가장 prior 값이 높은 column을 찾아서, for_scoring의 estimated_label 칼럼 값으로 넣는다.
# 일단 여기까지 해 보자.

results = pd.read_csv("result.csv", index_col=0)
method_name = results["name"]
zero_data = np.zeros(shape=(1000,1))
empty_vector = pd.DataFrame(zero_data, columns=["estimated label"], dtype="str")

for_scoring = pd.merge(method_name, empty_vector, left_index=True, right_index=True)

labeldict = {0:"src", 1:"sin", 2:"san", 3:"non"}

def findlabel():
    results_only_priors = results.drop("name", axis=1)
    i = 0
    for rowtuple in results_only_priors.itertuples(index=False):
        if rowtuple[0] == rowtuple[1] == rowtuple[2] == rowtuple[3]:
            for_scoring.at[i, "estimated label"] = "unscorable"
        else:
            label = labeldict[rowtuple.index(max(rowtuple))]
            for_scoring.at[i, "estimated label"] = label
        i += 1

findlabel()

for_scoring = for_scoring.loc[for_scoring["estimated label"] != "unscorable"]

# 아이고 맙소사 ID가 필요하잖아?

