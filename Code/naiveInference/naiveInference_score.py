import pandas as pd
import numpy as np

results = pd.read_csv("result.csv", index_col=0)
zero_data = np.zeros(shape=(1000, 1))
results_ids = results["id"]
empty_vector2 = pd.DataFrame(zero_data, columns=["label"], dtype="str")

for_scoring = pd.merge(results_ids, empty_vector2, left_index=True, right_index=True)

labeldict = {0: "src", 1: "sin", 2: "san", 3: "non"}

def findlabel():
    results_only_priors = results.drop("id", axis=1)
    i = 0
    for rowtuple in results_only_priors.itertuples(index=False):
        if rowtuple[0] == rowtuple[1] == rowtuple[2] == rowtuple[3]:
            for_scoring.at[i, "label"] = "unscorable"
        else:
            label = labeldict[rowtuple.index(max(rowtuple))]
            for_scoring.at[i, "label"] = label
        i += 1

findlabel()

src_condition = for_scoring["label"] == 'src'
sin_condition = for_scoring["label"] == 'sin'
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
    sources_and_sinks.at[i, 'id'] = info.split(',')[1].lstrip().strip(').\n').replace('"', '')  # 눈물겹다...
    if info.split('(')[0] == "TaintSourceMethod":
        sources_and_sinks.at[i, 'label'] = "src"
    elif info.split('(')[0] == "LeakingSinkMethod":
        sources_and_sinks.at[i, 'label'] = "sin"
    i += 1

# for_scoring에 있는 row가 sources_and_sinks에도 있는지를 확인
# https://stackoverflow.com/questions/38855204/check-if-a-row-in-one-data-frame-exist-in-another-data-frame

scores = pd.merge(for_scoring, sources_and_sinks, how='left', indicator='correct')
scores['correct'] = np.where(scores.correct == 'both', True, False)
