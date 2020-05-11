import pandas as pd
import time
import os

start = time.time()

methodInfo1 = pd.read_csv("raw_data.csv", index_col=0)
methodInfo2 = pd.read_csv("raw_data.csv", index_col=0)
methodInfo1 = methodInfo1.drop('id', axis=1)
methodInfo2 = methodInfo2.drop('id', axis=1)


# TODO: Dead 스트링의 끝에 )가 하나 남음
def tuple_string_to_tuple(tuple_string):
    string_list = tuple_string.split(", ")
    string_list[0] = string_list[0].lstrip('(')
    string_list[1] = string_list[1].rstrip(')')
    string_list[1] = string_list[1]+')'
    return (string_list[0], string_list[1])


def parse_chain(var_and_chain):
    var = var_and_chain[0]
    chain = var_and_chain[1]
    chain = chain.split(" -> ")
    chain = list(filter(lambda string: string != "", chain))
    chain = list(map(lambda item: item.lstrip(), chain))
    chain = list(map(lambda string: tuple_string_to_tuple(string), chain))
    return [var, chain]


def make_chain():
    path = os.path.abspath("..")
    path = os.path.join(path, "benchmarks", "fabricated", "Chain.txt")
    with open(path, "r+") as chainfile:
        lines = chainfile.readlines()
        var_to_chain = list(filter(lambda line: line != "\n", lines))
        var_to_chain = list(map(lambda line: line.rstrip(), var_to_chain))
        var_and_chain = list(map(lambda line: line.split(": "), var_to_chain))
        var_and_chain = list(map(lambda lst: parse_chain(lst), var_and_chain))
    return var_and_chain


def make_calledges():
    path = os.path.abspath("..")
    path = os.path.join(path, "benchmarks", "fabricated", "Callgraph.txt")
    with open(path, "r+") as callgraphfile:
        lines = callgraphfile.readlines()
        lines = list(filter(lambda line: "__new" not in line
                            and "<init>" not in line, lines))
        lines = list(map(lambda line: line.rstrip(), lines))
        lines = list(map(lambda line: line.split(" -> "), lines))
        call_edges = list(map(lambda lst: tuple(lst), lines))
    return call_edges


var_and_chain = make_chain()
call_edges = make_calledges()


def scoring_function(info1, info2):
    score = 0
    if info1[1] == info2[1]:  # The two methods belong to the same package
        score += 10
    if info1[2] == info2[2]:  # The two methods have a same return type 
        score += 10
    if (info1[3] in info2[3]) or (info2[3] in info1[3]) or (info1[3][0:2] == info2[3][0:2]) or (info1[3][0:2] == info2[3][0:2]):
        # The two methods start with a same prefix
        score += 10
    if info1[4] == info2[4]:  # The two methods have a same input type
        score += 10
    return score


def detect_dataflow():  # method1, method2
    out = []
    for [_, chain] in var_and_chain:
        for tup in chain:
            caller_name, activity = tup
            if "Call" in activity:
                tmplst = activity.split("with")[0].split("(")
                callee_name = tmplst[1]+"("+tmplst[2].rstrip()
                out.append((caller_name, callee_name))
            if "Define" in activity:
                callee_name = activity.split("using")[1]
                callee_name = callee_name.lstrip(" ")
                out.append((callee_name, caller_name))
    out = list(filter(lambda tup: None not in tup, out))
    return out


dataflow_edges = detect_dataflow()


def output_dfedges():
    global dataflow_edges
    with open("df.txt", "w+") as df:
        for (dfsend, dfrcv) in dataflow_edges:
            df.write(dfsend + ", " + dfrcv + "\n")


def output_calledges():
    global call_edges
    with open("callg.txt", "w+") as call:
        for (caller, callee) in call_edges:
            call.write(caller + ", " + callee + "\n")


def output_alledges():
    output_dfedges()
    output_calledges()


output_alledges()


def there_is_dataflow(info1, info2):
    intype1 = "()" if info1[4] == "void" else "("+info1[4]+")"
    id1 = info1[2]+" "+info1[1]+"."+info1[3]+intype1
    intype2 = "()" if info2[4] == "void" else "("+info2[4]+")"
    id2 = info2[2]+" "+info2[1]+"."+info2[3]+intype2
    if (id1, id2) in dataflow_edges:
        return True
    else:
        return False


def there_is_calledge(info1, info2):
    intype1 = "()" if info1[4] == "void" else "("+info1[4]+")"
    id1 = info1[2]+" "+info1[1]+"."+info1[3]+intype1
    intype2 = "()" if info2[4] == "void" else "("+info2[4]+")"
    id2 = info2[2]+" "+info2[1]+"."+info2[3]+intype2
    if (id1, id2) in call_edges:
        return True
    else:
        return False


print("starting bottleneck")  # ================
edge1 = []
edge2 = []

for row1 in methodInfo1.itertuples(index=False):
    for row2 in methodInfo2.itertuples(index=False):
        if there_is_dataflow(row1, row2) or\
           there_is_calledge(row1, row2) or\
           scoring_function(row1, row2) > 20:
            edge1.append(row1)
            edge2.append(row2)
print("completed bottleneck")  # ================


edge1 = pd.DataFrame(edge1, columns=methodInfo1.columns)
edge2 = pd.DataFrame(edge2, columns=methodInfo2.columns)
edges = pd.merge(edge1, edge2, left_index=True, right_index=True)
edges.columns = pd.MultiIndex.from_product([['edge1', 'edge2'],
                                            methodInfo1.columns])


def no_symmetric(dataframe):
    dataframe['temp'] = dataframe.index * 2
    dataframe2 = dataframe.iloc[:, [5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 10]]
    dataframe2.columns = dataframe.columns
    dataframe2['temp'] = dataframe2.index * 2 + 1
    out = pd.concat([dataframe, dataframe2])
    out = out.sort_values(by='temp')
    out = out.set_index('temp')
    out = out.drop_duplicates()
    out = out[out.index % 2 == 0]
    out = out.reset_index()[['edge1', 'edge2']]
    return out


def no_reflexive(dataframe):
    cond1 = dataframe[('edge1', 'index')] != dataframe[('edge2', 'index')]
    cond2 = dataframe[('edge1', 'pkg')] != dataframe[('edge2', 'pkg')]
    cond3 = dataframe[('edge1', 'rtntype')] != dataframe[('edge2', 'rtntype')]
    cond4 = dataframe[('edge1', 'name')] != dataframe[('edge2', 'name')]
    cond5 = dataframe[('edge1', 'intype')] != dataframe[('edge2', 'intype')]
    return dataframe[cond1 | cond2 | cond3 | cond4 | cond5]


def test_reflexive(dataframe):
    reflex1 = dataframe[('edge1', 'index')] == dataframe[('edge2', 'index')]
    reflex2 = dataframe[('edge1', 'pkg')] == dataframe[('edge2', 'pkg')]
    reflex3 = dataframe[('edge1', 'rtntype')] == dataframe[('edge2', 'rtntype')]
    reflex4 = dataframe[('edge1', 'name')] == dataframe[('edge2', 'name')]
    reflex5 = dataframe[('edge1', 'intype')] == dataframe[('edge2', 'intype')]
    return dataframe[reflex1 & reflex2 & reflex3 & reflex4 & reflex5]


edges_new = no_reflexive(no_symmetric(edges))  # for Bayesian Networks: directed graphs
# edges_new = no_reflexive(edges) # for Markov Random Fields: undirected graphs

edges_new.to_csv("edges.csv", mode='w')

print("elapsed time: ", time.time()-start)
