import json
import pandarallel
import pandas as pd
import re
import os.path

from collections import Counter
from functools import reduce

# Utility Funcs ========================
# ======================================

NODE_DATA = pd.read_csv("nodes.csv", index_col=0)
DF = pd.read_csv("df.csv", index_col=0)
CALL = pd.read_csv("callg.csv", index_col=0)
CALLGRAPH = CALL[["id1", "id2"]]


def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]


PROJECT_ROOT_DIR = retrieve_path()


def load_chain_json():
    """Parse the whole Chain.json into a DataFrame"""
    path = os.path.join(PROJECT_ROOT_DIR, "Chain.json")
    return pd.read_json(path)


CHAIN = load_chain_json()


def filtermethod(string):
    return "$" not in string and\
           "__" not in string and\
           "<init>" not in string and\
           "<clinit>" not in string and\
           "lambda" not in string and\
           "Lambda" not in string


# https://stackoverflow.com/questions/29916065/how-to-do-camelcase-split-in-python
def camel_case_split(identifier):
    matches = re.finditer('.+?(?:(?<=[a-z])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])|$)', identifier)
    return [m.group(0) for m in matches]


def find_frequent_words(**kwargs):
    """available kwargs:
       - target: 'name', 'rtntype'"""
    if kwargs["target"] == 'name':
        node_names = NODE_DATA[kwargs["target"]]
        splitted_names = node_names.apply(camel_case_split)
        splitted_names = [value for _, value in splitted_names.iteritems()]
        words_withdup = reduce(lambda acc, elem: acc+elem, splitted_names, [])
        words_withdup = list(map(lambda name: name.lower(), words_withdup))
        words_nodup = set(words_withdup)
        acc = []
        for name in words_nodup:
            acc.append((name, words_withdup.count(name)))
        return sorted(acc, key=lambda x: x[1], reverse=True)

    elif kwargs["target"] == 'rtntype':
        node_rtntypes = NODE_DATA[kwargs["target"]]
        splitted_rtntypes = node_rtntypes.apply(camel_case_split)
        splitted_rtntypes = [value for _, value in splitted_rtntypes.iteritems()]
        words_withdup = reduce(lambda acc, elem: acc+elem, splitted_rtntypes, [])
        words_withdup = list(map(lambda name: name.lower(), words_withdup))
        words_withdup = list(filter(lambda name: name not in JAVA_BUILTIN_TYPES, words_withdup))
        words_nodup = set(words_withdup)
        acc = []
        for name in words_nodup:
            acc.append((name, words_withdup.count(name)))
        return sorted(acc, key=lambda x: x[1], reverse=True)


def flatten(ll):
    return [elem for lst in ll for elem in lst]


def preprocess_intype(raw_intypes):
    def mapfunc(string):
        if "," in string:
            return string.split(", ")
        else:
            return string
    return flatten(list(map(mapfunc, raw_intypes)))


def find_frequents(**kwargs):
    if kwargs["target"] == "rtntype":
        node_rtntypes = NODE_DATA["rtntype"]
        counterobj = Counter(node_rtntypes)
        most_commons = counterobj.most_common(10)
        return sorted(most_commons, key=lambda x: x[1], reverse=True)

    elif kwargs["target"] == "intype":
        node_intypes = preprocess_intype(NODE_DATA["intype"])
        counterobj = Counter(node_intypes)
        most_commons = counterobj.most_common(10)
        return sorted(most_commons, key=lambda x: x[1], reverse=True)

    elif kwargs["target"] == "callees":
        top10 = CALLGRAPH.id1.value_counts().head(10)
        return list(top10.index)


# Parameters =============================
# ========================================


TOP_FREQ_N_NAME_WORDS = 10            # name 낱말의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_RTNTYPE_WORDS = 10         # rtntype 낱말의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_CLASSNAME_WORDS = 10       # class 낱말의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_RTNTYPES = 10              # rtntype을 통째로 생각했을 때, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_INTYPES = 10               # intypes 낱말의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_CALLEES = 10               # callee들의 경우, 상위 몇 순위까지 고려할 거냐?


# Constants ============================
# ======================================


# TODO: get, set 등 식상한 이름들과 JAVA_BUILTIN_TYPES를 제외한 목록에서 frequent 찾기

with open("java_builtin_types.txt", "r+") as builtintypes:
    JAVA_BUILTIN_TYPES = list(map(lambda string: string.rstrip(),
                                  builtintypes.readlines()))
TOP_FREQ_NAME_WORDS = list(map(lambda tup: tup[0],
                               find_frequent_words(target="name")[:TOP_FREQ_N_NAME_WORDS]))
TOP_FREQ_RTNTYPE_WORDS = list(map(lambda tup: tup[0],
                                  find_frequent_words(target="rtntype")[:TOP_FREQ_N_RTNTYPE_WORDS]))
TOP_FREQ_CLASSNAME_WORDS = list(map(lambda tup: tup[0],
                                    find_frequent_words(target="rtntype")[:TOP_FREQ_N_CLASSNAME_WORDS]))
TOP_FREQ_RTNTYPES = list(map(lambda tup: tup[0],
                             find_frequents(target="rtntype")[:TOP_FREQ_N_RTNTYPES]))
TOP_FREQ_INTYPES = list(map(lambda tup: tup[0],
                            find_frequents(target="intype")[:TOP_FREQ_N_INTYPES]))
TOP_FREQ_CALLEES = list(map(lambda tup: tup[0],
                            find_frequents(target="callees")[:TOP_FREQ_N_CALLEES]))


# Syntactic Features =====================
# ========================================
# the parameter "node" stands for a row in NODE_DATA


def has_parameters(node):
    """Does this method have parameters?"""
    return node.intype != "void"


def has_return_type(node):
    """Does this method have a return type?"""
    return node.rtntype != "void"


def method_name_starts_with(node):
    """Does this method's name start with the given word?
       NOTE Higher-order feature"""
    prefix = camel_case_split(node[3])[0]
    out = dict()
    for freq_word in TOP_FREQ_NAME_WORDS:
        out[("method_name_starts_with", freq_word)] = prefix == freq_word
    return out    # key: word, val: boolean


def method_name_contains(node):
    """Does this method's name contain the given word?
       NOTE Higher-order feature"""
    words = camel_case_split(node[3])
    out = dict()
    for freq_word in TOP_FREQ_NAME_WORDS:
        out[("method_name_contains", freq_word)] = freq_word in words
    return out    # key: word, val: boolean


def return_type_contains_name(node):
    """Does the return type contain the given name?
       NOTE Higher-order feature"""
    words = camel_case_split(node[2])
    out = dict()
    for freq_word in TOP_FREQ_RTNTYPE_WORDS:
        out[("return_type_contains_name", freq_word)] = freq_word in words
    return out    # key: word, val: boolean


def class_contains_name(node):
    """Is the method part of class that contains the given name?
       NOTE Higher-order feature"""
    words = camel_case_split(node[1])
    out = dict()
    for freq_word in TOP_FREQ_CLASSNAME_WORDS:
        out[("class_contains_name", freq_word)] = freq_word in words
    return out    # key: word, val: boolean


def class_endswith_name(node):
    """Is the method part of class that ends with the given name?
       NOTE Higher-order feature"""
    words = camel_case_split(node[1])
    suffix = camel_case_split(node[1])[len(words)-1]
    out = dict()
    for freq_word in TOP_FREQ_CLASSNAME_WORDS:
        out[("class_endswith_name", freq_word)] = suffix == freq_word
    return out


def rtntype_equals(node):
    """Is the return type of the method equal to the type given?
       NOTE Higher-order feature"""
    rtntype = node[2]
    out = dict()
    for freq_rtntype in TOP_FREQ_RTNTYPES:
        out[("returntype_equals", "")] = rtntype == freq_rtntype
    return out


def param_contains_type_or_name(node):
    """Do any of the parameters' type contain the given name?
       NOTE Higher-order feature"""
    intypes = node[4].split(",")
    out = dict()
    for freq_intype in TOP_FREQ_INTYPES:
        out[("param_contains_type_or_name", "")] =\
            reduce(lambda acc, elem: elem == freq_intype or acc, False)
    return out


def param_type_matches_return_type(node):
    """Does any of the parameters match the return type?
       NOTE Higher-order feature"""
    rtntype = node[2]
    intypes = node[4].split(",")
    return rtntype in intypes


def is_real_setter(node):
    """Feature that checks whether the current method begins with "get", and there
       is a corresponding "set" method in the class."""
    methname = node[3]
    classname = node[1]
    if camel_case_split(methname)[0] == "get":
        same_class_rows = NODE_DATA[NODE_DATA["class"] == classname]
        for row in same_class_rows.itertuples():
            other_name = row[4]
            if other_name == "set"+other_name[3:]:
                return True
    else:
        return False


def void_on_method(node):
    """Feature that matches whenever a method returns void and the method name starts
       with "on"."""
    return camel_case_split(node[3]) == "on" and node[2] == "void"


def method_name_contains_return_type(node):
    """Does the method name contain the return type?"""
    rtntype = node[2]
    methname = node[3]
    return rtntype in camel_case_split(methname)


# Semantic Features ==================
# ====================================


list_of_callers = list(CALLGRAPH["id1"])
list_of_callees = list(CALLGRAPH["id2"])
list_of_data_passers = list(DF["id1"])
list_of_data_passees = list(DF["id2"])


def invocation_name(node):
    """Check if an invocation to a certain method is made."""
    # take a look at the callgraph
    methname = node[3]
    out = dict()
    for freq_callee in TOP_FREQ_CALLEES:
        selected_rows = CALLGRAPH[(CALLGRAPH["id1"] == methname) &
                                  (CALLGRAPH["id2"] == freq_callee)]
        out[("invocation_name", freq_callee)] = not selected_rows.empty
    return out


def calling_but_no_df(node):
    """Is this method calling another method, but not passing any data to it?"""
    methname = node[3]
    node_is_caller = methname in list_of_callers
    not_passing_data = methname not in list_of_data_passers
    return node_is_caller and not_passing_data


def called_but_no_df(node):
    """Has this method been called, but are there no other data flowing into it?"""
    methname = node[3]
    node_is_callee = methname in list_of_callees
    not_being_passed_data = methname not in list_of_data_passees
    return node_is_callee and not_being_passed_data


def making_df_call(node):
    """Is this method calling other method and passing data at the same time?"""
    methname = node[3]
    node_is_caller = methname in list_of_callers
    passing_data = methname in list_of_data_passers
    return node_is_caller and passing_data


def has_df_call(node):
    """Is this method being called and being passed data at the same time?"""
    methname = node[3]
    node_is_callee = methname in list_of_callees
    being_passed_data = methname in list_of_data_passees
    return node_is_callee and being_passed_data


def receiving_and_passing_data(node):
    """Is this method receiving and passing data at the same time?"""
    methname = node[3]
    being_passed_data = methname in list_of_data_passees
    passing_data = methname in list_of_data_passers
    return being_passed_data and passing_data


def has_df_call_and_dead(node):
    """Are any pieces of data being passed to this method via call
       and being dead in this method?"""
    methname = node[3]
    def mapfunc(chain):
        for event in chain:
            if event["status"] == "Dead":
                current_method = event["current_method"]
                for event in chain:
                    if event["status"] == "Call" and\
                       event["callee"] == current_method:
                        return True
        return False
    return CHAIN["chain"].apply(mapfunc).any()


def has_redefine(node):
    """Are there any data redefinitions in this method?"""
    methname = node[3]
    def mapfunc(chain):
        for event in chain:
            if event["status"] == "redefine" and\
               event["current_method"] == methname:
                return True
        return False
    return CHAIN["chain"].apply(mapfunc).any()


# Batch run ==========================
# ====================================


def run_all_extractors(node_row):
    """batch run the feature extractors on a method"""
    id_df = pd.DataFrame([[node_row[5]]],    # the id of the method
                         columns=pd.MultiIndex.from_tuples([("id", "")]))

    has_parameters_df = pd.DataFrame([has_parameters(node_row)],
                          columns=pd.MultiIndex.from_tuples([("has_parameters", "")]))

    has_return_type_df = pd.DataFrame([has_return_type(node_row)],
                          columns=pd.MultiIndex.from_tuples([("has_return_type", "")]))

    method_name_starts_with_df = pd.DataFrame(method_name_starts_with(node_row), index=[0])

    method_name_contains_df = pd.DataFrame(method_name_contains(node_row), index=[0])

    return_type_contains_name_df = pd.DataFrame(return_type_contains_name(node_row), index=[0])

    vector = pd.concat([ id_df,
                         has_parameters_df,
                         has_return_type_df,
                         method_name_starts_with_df,
                         method_name_contains_df,
                         return_type_contains_name_df ], axis=1)

    return vector


# main ================================
# =====================================


def main():
    sim_df = pd.DataFrame()
    for tup in NODE_DATA.itertuples(index=False):  # 크기가 작으니까 가능한 거다
        vector = run_all_extractors(tup)
        sim_df = pd.concat([sim_df, vector])
    sim_df.to_csv("sim_vectors.csv", mode="w+")


if __name__ == "__main__":
    main()
