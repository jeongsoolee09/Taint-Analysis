import pandas as pd
import time

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


print("starting bottleneck") # ================
edge1 = []
edge2 = []

for row1 in methodInfo1.itertuples(index=False):
    for row2 in methodInfo2.itertuples(index=False):
        if scoring_function(row1, row2) >= 20:
            edge1.append(row1)
            edge2.append(row2)
print("completed bottleneck") # ================


edge1 = pd.DataFrame(edge1, columns = methodInfo1.columns)
edge2 = pd.DataFrame(edge2, columns = methodInfo2.columns)
edges = pd.merge(edge1, edge2, left_index=True, right_index=True)
edges.columns = pd.MultiIndex.from_product([['edge1', 'edge2'], methodInfo1.columns])

def no_symmetric(dataframe):
    dataframe['temp'] = dataframe.index * 2
    dataframe2 = dataframe.iloc[:, [5,6,7,8,9,0,1,2,3,4,10]]
    dataframe2.columns = dataframe.columns
    dataframe2['temp'] = dataframe2.index * 2 + 1
    out = pd.concat([dataframe, dataframe2])
    out = out.sort_values (by='temp')
    out = out.set_index('temp')
    out = out.drop_duplicates()
    out = out[out.index%2 == 0]
    out = out.reset_index()[['edge1', 'edge2']]

    return out

def no_reflexive(dataframe):
    cond1 = dataframe[('edge1','index')] != dataframe[('edge2','index')]
    cond2 = dataframe[('edge1','pkg')] != dataframe[('edge2','pkg')]
    cond3 = dataframe[('edge1','rtntype')] != dataframe[('edge2','rtntype')]
    cond4 = dataframe[('edge1','name')] != dataframe[('edge2','name')]
    cond5 = dataframe[('edge1','intype')] != dataframe[('edge2','intype')]

    return dataframe[cond1 | cond2 | cond3 | cond4 | cond5] # DeMorgan FLEX

edges = no_reflexive(no_symmetric(edges)) # for Bayesian Networks: directed graphs
# edges = no_reflexive(edges) # for Markov Random Fields: undirected graphs

edges.to_csv("edges.csv", mode='w')

print("elapsed time: ", time.time()-start)
