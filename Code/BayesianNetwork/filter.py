import modin.pandas as pd
import time
import os
import json
from multiprocessing import Pool
from main import process


def make_dataframes():
    methodInfo1 = pd.read_csv("raw_data.csv", index_col=0)
    methodInfo2 = pd.read_csv("raw_data.csv", index_col=0)

    methodInfo1 = methodInfo1.drop('id', axis=1)
    methodInfo2 = methodInfo2.drop('id', axis=1)

    # renaming columns for producing cartesian product by merging
    methodInfo1 = methodInfo1.rename(columns={'index':'index1', 'pkg':'pkg1',
                                              'rtntype':'rtntype1', 'name':'name1',
                                              'intype':'intype1'})
    methodInfo2 = methodInfo2.rename(columns={'index':'index2', 'pkg':'pkg2',
                                              'rtntype':'rtntype2', 'name':'name2',
                                              'intype':'intype2'})
    # Creating a key column for merging
    methodInfo1['key'] = 1
    methodInfo2['key'] = 1

    carPro = pd.merge(methodInfo1, methodInfo2, how='outer')
    carPro = carPro.drop('key', axis=1)

    # restoring column names
    methodInfo1 = methodInfo1.rename(columns={'index1':'index', 'pkg1':'pkg',
                                              'rtntype1':'rtntype', 'name1':'name',
                                              'intype1':'intype'})
    methodInfo2 = methodInfo2.rename(columns={'index2':'index', 'pkg2':'pkg',
                                              'rtntype2':'rtntype', 'name2':'name',
                                              'intype2':'intype'})
    return methodInfo1, methodInfo2, carPro


methodInfo1, methodInfo2, carPro = make_dataframes()


def filtermethod(string):
    return "__" not in string and\
        "<init>" not in string and\
        "<clinit>" not in string and\
        "lambda" not in string and\
        "Lambda" not in string


def load_chain_json():
    """Chain.json을 통째로 파싱해 파이썬 자료구조에 담는다. 결과값은 리스트이다."""
    path = os.path.abspath("..")
    path = os.path.join(path, "benchmarks", "realworld", "sagan", "Chain.json")
    with open(path, "r+") as chainjson:
        wrapped_chain_list = json.load(chainjson)
    return wrapped_chain_list


def make_wrapped_chains():
    """Chain.json을 읽고, toplevel list에 있는 각 json 객체를 처리한다."""
    raw_wrapped_chain_list = load_chain_json()
    wrapped_chains = list(map(process_wrapped_chain_slice, raw_wrapped_chain_list))
    return wrapped_chains


def process_wrapped_chain_slice(wrapped_chain):
    """각 리스트 안에 들어 있는, defining method와 access_path로 chain"""
    defining_method_tup, access_path_tup, chain_tup = wrapped_chain.items()
    defining_method = defining_method_tup[1]
    access_path = access_path_tup[1]
    chain = chain_tup[1]  # this is a list
    dm_ap_mangled = "("+defining_method+", "+access_path+")"
    chain = list(map(process_bare_chain_slice, chain))  # use multiprocessing.map!
    return (dm_ap_mangled, chain)
    

def process_bare_chain_slice(chain_slice):
    """json의 chain attribute의 값으로 들어 있던 리스트 안에 들어 있는 chain slice를 처리"""
    if chain_slice["status"] == "Define":
        current_method_tup, status_tup,\
            access_path_tup, callee_tup = chain_slice.items()
        current_method = current_method_tup[1]
        status = status_tup[1]
        access_path = access_path_tup[1]
        callee = callee_tup[1]
        msg = status + " (" + access_path + " using " + callee + ")"
        return (current_method, msg)
    elif chain_slice["status"] == "Call":
        current_method_tup, status_tup,\
            callee_tup, ap_tup = chain_slice.items()
        current_method = current_method_tup[1]
        status = status_tup[1]
        callee = callee_tup[1]
        ap = ap_tup[1]
        msg = status + " (" + callee + " with " + ap
        return (current_method, msg)
    elif chain_slice["status"] == "Redefine":
        current_method_tup, status_tup, access_path_tup = chain_slice.items()
        current_method = current_method_tup[1]
        status = status_tup[1]
        access_path = access_path_tup[1]
        msg = status + " ("+access_path  # sigh... an unmatched parens..
        return (current_method, msg)
    elif chain_slice["status"] == "Dead":
        current_method_tup, status_tup = chain_slice.items()
        current_method = current_method_tup[1]
        status = status_tup[1]
        msg = status
        return (current_method, msg)


def make_calledges():
    path = os.path.abspath("..")
    path = os.path.join(path, "benchmarks", "realworld", "sagan", "Callgraph.txt")
    with open(path, "r+") as callgraphfile:
        lines = callgraphfile.readlines()
        lines = list(filter(lambda line: "__new" not in line
                            and "<init>" not in line, lines))
        lines = list(map(lambda line: line.rstrip(), lines))
        lines = list(map(lambda line: line.split(" -> "), lines))
        call_edges = list(map(lambda lst: tuple(lst), lines))
        call_edges = list(map(lambda tup: (process(tup[0]), process(tup[1])), call_edges))
    return call_edges


def scoring_function(info1, info2):
    score = 0
    if info1[1] == info2[1]:  # The two methods belong to the same package
        score += 10
    if info1[2] == info2[2]:  # The two methods have a same return type
        score += 10
    if (info1[3] in info2[3]) or (info2[3] in info1[3]) or\
       (info1[3][0:2] == info2[3][0:2]) or (info1[3][0:2] == info2[3][0:2]):
        # The two methods start with a same prefix
        score += 10
    if info1[4] == info2[4]:  # The two methods have a same input type
        score += 10
    return score


def detect_dataflow(var_and_chain):  # method1, method2
    dataflow_edges = []
    for chain in var_and_chain.values():
        for tup in chain:
            caller_name, activity = tup
            if "Call" in activity:
                tmplst = activity.split(" with ")[0].split("(")
                callee_name = tmplst[1]+"("+tmplst[2].rstrip()
                dataflow_edges.append((caller_name, callee_name))
            if "Define" in activity:
                callee_name = activity.split("using")[1]
                callee_name = callee_name.lstrip(" ")
                dataflow_edges.append((caller_name, callee_name))
    dataflow_edges = list(filter(lambda tup: None not in tup, dataflow_edges))
    dataflow_edges = list(filter(lambda tup: filtermethod(tup[0]) and filtermethod(tup[1]), dataflow_edges))
    dataflow_edges = list(map(lambda tup: (process(tup[0]), process(tup[1])), dataflow_edges))
    return dataflow_edges


def output_dfedges(dataflow_edges):
    with open("df.txt", "w+") as df:
        for (dfsend, dfrcv) in dataflow_edges:
            df.write(dfsend + ", " + dfrcv + "\n")


def output_calledges(call_edges):
    with open("callg.txt", "w+") as call:
        for (caller, callee) in call_edges:
            call.write(caller + ", " + callee + "\n")


def output_alledges(dataflow_edges, call_edges):
    output_dfedges(dataflow_edges)
    output_calledges(call_edges)


def there_is_dataflow(dataflow_edges, info1, info2):
    intype1 = "()" if info1[4] == "void" else "("+info1[4]+")"
    id1 = info1[2]+" "+info1[1]+"."+info1[3]+intype1
    intype2 = "()" if info2[4] == "void" else "("+info2[4]+")"
    id2 = info2[2]+" "+info2[1]+"."+info2[3]+intype2
    if (id1, id2) in dataflow_edges:
        return True
    else:
        return False


def there_is_calledge(call_edges, info1, info2):
    intype1 = "()" if info1[4] == "void" else "("+info1[4]+")"
    id1 = info1[2]+" "+info1[1]+"."+info1[3]+intype1
    intype2 = "()" if info2[4] == "void" else "("+info2[4]+")"
    id2 = info2[2]+" "+info2[1]+"."+info2[3]+intype2
    if (id1, id2) in call_edges:
        return True
    else:
        return False


def there_is_already_an_edge_between(row1, row2, edgelist):
    if (row1, row2) in edgelist or (row2, row1) in edgelist:
        return True
    else:
        return False


def find_that_edge_between(row1, row2, edgelist):
    if (row1, row2) in edgelist:
        return (row1, row2)
    elif (row2, row1) in edgelist:
        return (row2, row1)


# 이중 for loop 타도하자!!
def add_edges(methodInfo1, methodInfo2, dataflow_edges, call_edges):
    edgelist = []
    for row1 in methodInfo1.itertuples(index=False):
        for row2 in methodInfo2.itertuples(index=False):
            if there_is_dataflow(dataflow_edges, row1, row2):
                if there_is_already_an_edge_between(row1, row2, edgelist):
                    # edge = find_that_edge_between(row1, row2, edgelist)
                    # edgelist.remove(edge)
                    continue
                edgelist.append((row1, row2))
            else:
                if there_is_calledge(call_edges, row1, row2):
                    edgelist.append((row1, row2))
                else:
                    if scoring_function(row1, row2) > 20:
                        edgelist.append((row1, row2))
    return edgelist


def make_multicolumn(methodInfo1, methodInfo2, edge1, edge2):
    edge1 = list(edge1)
    edge2 = list(edge2)
    edge1 = pd.DataFrame(edge1, columns=methodInfo1.columns)
    edge2 = pd.DataFrame(edge2, columns=methodInfo2.columns)
    edges = pd.merge(edge1, edge2, left_index=True, right_index=True)
    edges.columns = pd.MultiIndex.from_product([['edge1', 'edge2'],
                                                methodInfo1.columns])
    return edges


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
    reflex3 = dataframe[('edge1', 'rtntype')] == dataframe[('edge2',
                                                            'rtntype')]
    reflex4 = dataframe[('edge1', 'name')] == dataframe[('edge2', 'name')]
    reflex5 = dataframe[('edge1', 'intype')] == dataframe[('edge2', 'intype')]
    return dataframe[reflex1 & reflex2 & reflex3 & reflex4 & reflex5]


def main():
    methodInfo1, methodInfo2, carPro = make_dataframes() # the main data we are manipulating
    wrapped_chain_list = load_chain_json()
    var_and_chain = dict(make_wrapped_chains())
    dataflow_edges = detect_dataflow(var_and_chain)
    call_edges = make_calledges()
    output_alledges(dataflow_edges, call_edges)
    return dataflow_edges, call_edges, methodInfo1, methodInfo2, carPro


if __name__ == "__main__":
    start = time.time()
    dataflow_edges, call_edges, methodInfo1, methodInfo2, carPro = main()
    
    edgelist = add_edges(methodInfo1, methodInfo2, dataflow_edges, call_edges)
    print('done multiprocessing')
    [edge1, edge2] = zip(*edgelist)
    make_multicolumn(methodInfo1, methodInfo2, edge1, edge2)
    edges_new = no_reflexive(no_symmetric(edges))
    edges_new.to_csv("edges.csv", mode='w')
    print("elapsed time: ", time.time()-start)

