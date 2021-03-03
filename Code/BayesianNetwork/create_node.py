import pandas as pd
import time
import re
import os.path
import json


regex = r'\((.*)\)'
regex = re.compile(regex)


class ProcessingError(Exception):
    def __init__(self, string):
        self.string = string


def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]


PROJECT_ROOT_DIR = retrieve_path()


def flatten(ll):
    flat_list = []
    for sublist in ll:
        for item in sublist:
            flat_list.append(item)
    return flat_list


def filtermethod(string):
    return "$" not in string and\
           "__" not in string and\
           "<init>" not in string and\
           "<clinit>" not in string and\
           "lambda" not in string and\
           "Lambda" not in string


def process(method_id):
    """splits a method id into (classname, rtntype, methodname, intype, id)"""
    try:
        space_index = method_id.index(' ')
    except ValueError:
        raise ProcessingError("create_node.process() failed on: " + method_id)
    split_on_open_paren = method_id.split('(')
    last_dot_index = split_on_open_paren[0].rindex('.')
    open_paren_index = method_id.index('(')
    rtntype = method_id[:space_index]
    class_ = method_id[space_index+1:last_dot_index]
    name = method_id[last_dot_index+1:open_paren_index]
    intype = regex.findall(method_id)[0]
    if intype == '':
        intype = 'void'
    return (class_, rtntype, name, intype, method_id)


def populate_sofallm(methodfile, callgraphfile):
    setofallmethods = []
    methods = []
    callmethods = []
    with open(methodfile, "r+") as f:
        for line in f.readlines():
            methods.append(line.rstrip())
    methods = list(filter(filtermethod, methods))
    methods = set(methods)
    with open(callgraphfile, "r+") as g:
        for line in g.readlines():
            callmethods.append(line.rstrip())
    callmethods = list(filter(filtermethod, callmethods))
    callmethods = list(map(lambda line: line.rstrip(), callmethods))
    callmethods = list(map(lambda line: line.split(" -> "), callmethods))
    callmethods = set(flatten(callmethods))
    setofallmethods = list(methods.union(callmethods))
    setofallmethods = list(filter(lambda meth: ' ' in meth, setofallmethods))

    setofallmethods = list(map(process, setofallmethods))
    return setofallmethods


def write_to_csv(setofallmethods):
    write_list = setofallmethods
    columns = ["class", "rtntype", "name", "intype", "id"]
    write_list = pd.DataFrame(write_list, columns=columns, dtype="str")
    write_list = write_list.reset_index()  # embed the index into a separate column
    write_list.to_csv("nodes.csv", mode='w+')


def main():
    start = time.time()

    # let's read the files created by static analysis
    methodfile = os.path.join(PROJECT_ROOT_DIR, 'skip_func.txt')
    callgraphfile = os.path.join(PROJECT_ROOT_DIR, 'Callgraph.txt')

    setofallmethods = populate_sofallm(methodfile, callgraphfile)
    write_to_csv(setofallmethods)

    print("elapsed time :", time.time() - start)


if __name__ == "__main__":
    main()
