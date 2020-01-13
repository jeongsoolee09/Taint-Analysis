import pandas as pd
import numpy as np
import re

results = pd.read_csv("result.csv", index_col=0)
ids = pd.read_csv("id.csv", index_col=0)
method_name = ids["id"]
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

src_condition = for_scoring["estimated label"] == 'src'
sin_condition = for_scoring["estimated label"] == 'sin'
for_scoring = for_scoring[src_condition | sin_condition]

# Parsing android-sources-and-sinks.txt

sas = open("/home/jslee/taint/doop/souffle-logic/addons/information-flow/android-sources-and-sinks.txt", "r+")
sas = sas.readlines()
i = len(sas) * 2
tempvec = np.arange(i)
sources_and_sinks = pd.DataFrame(tempvec.reshape(-1, 2), dtype="str")
sources_and_sinks.columns = ["id", "label"]

i = 0
for info in sas:
    sources_and_sinks.at[i, 'id'] = info.split(',')[1].lstrip().strip(').\n').replace('"', '') # 눈물겹다...
    if info.split('(')[0] == "TaintSourceMethod":
        sources_and_sinks.at[i, 'label'] = "src"
    elif info.split('(')[0] == "LeakingSinkMethod":
        sources_and_sinks.at[i, 'label'] = "sin"
    i += 1
