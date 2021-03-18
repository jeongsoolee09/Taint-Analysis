import json
import pandas as pd
import re
import os.path
import matplotlib.pyplot as plt

from collections import Counter
from functools import reduce
from itertools import repeat
from pandarallel import pandarallel


pandarallel.initialize()


# Files ================================
# ======================================

with open("java_builtin_types.txt", "r+") as builtintypes:
    JAVA_BUILTIN_TYPES = list(map(lambda string: string.rstrip(),
                                  builtintypes.readlines()))

with open("java_builtin_classes.txt", "r+") as builtinclasses:
    JAVA_BUILTIN_CLASSES = list(map(lambda string: string.rstrip(),
                                    builtinclasses.readlines()))

with open("java_builtin_collections.txt", "r+") as builtincollections:
    JAVA_BUILTIN_COLLS = list(map(lambda string: string.rstrip(),
                                  builtincollections.readlines()))

with open("java_builtin_utils.txt", "r+") as builtinutils:
    JAVA_BUILTIN_UTILS = list(map(lambda string: string.rstrip(),
                                  builtinutils.readlines()))

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


def exclude_first_last(lst):
    return lst[1:len(lst)-1]


def find_frequent_words(**kwargs):
    """available kwargs:
       - target: 'name', 'rtntype'"""
    if kwargs["target"] == "name-prefix":
        node_names = NODE_DATA["name"]
        splitted_names = node_names.parallel_apply(camel_case_split)
        splitted_names = [value for _, value in splitted_names.iteritems()]
        words_withdup = list(map(lambda elem: elem[0], splitted_names))
        words_withdup = list(filter(lambda name: name not in JAVA_BUILTIN_TYPES and\
                                    name not in JAVA_BUILTIN_CLASSES,#and\
                                    # name not in JAVA_BUILTIN_COLLS and\
                                    # name not in JAVA_BUILTIN_UTILS,
                                    words_withdup))
        words_nodup = set(words_withdup)
        acc = []
        for name in words_nodup:
            acc.append((name, words_withdup.count(name)))
        return sorted(acc, key=lambda x: x[1], reverse=True)

    elif kwargs["target"] == "name":
        node_names = NODE_DATA["name"]
        splitted_names = node_names.parallel_apply(camel_case_split)
        splitted_names = [value for _, value in splitted_names.iteritems()]
        words_withdup =\
            reduce(lambda acc, elem: acc+exclude_first_last(elem),  # exclude prefixes and suffixes
                   splitted_names, [])
        words_withdup = list(filter(lambda name: name not in JAVA_BUILTIN_TYPES and\
                                    name not in JAVA_BUILTIN_CLASSES,#and\
                                    # name not in JAVA_BUILTIN_COLLS and\
                                    # name not in JAVA_BUILTIN_UTILS,
                                    words_withdup))
        words_withdup = list(map(lambda word: word.lower(), words_withdup))
        # exclude common word such as "get" and "set"
        words_withdup = list(filter(lambda word: word != "get" and word != "set",
                                    words_withdup))
        words_nodup = set(words_withdup)
        acc = []
        for name in words_nodup:
            acc.append((name, words_withdup.count(name)))
        return sorted(acc, key=lambda x: x[1], reverse=True)

    elif kwargs["target"] == "rtntype-prefix":
        node_rtntypes = NODE_DATA["rtntype"]
        splitted_rtntypes = node_rtntypes.parallel_apply(camel_case_split)
        splitted_rtntypes = [value for _, value in splitted_rtntypes.iteritems()]
        words_withdup = list(map(lambda elem: elem[0], splitted_rtntypes))
        words_withdup = list(filter(lambda name: name not in JAVA_BUILTIN_TYPES and\
                                    name not in JAVA_BUILTIN_CLASSES,#and\
                                    # name not in JAVA_BUILTIN_COLLS and\
                                    # name not in JAVA_BUILTIN_UTILS,
                                    words_withdup))
        words_nodup = set(words_withdup)
        acc = []
        for name in words_nodup:
            acc.append((name, words_withdup.count(name)))
        return sorted(acc, key=lambda x: x[1], reverse=True)

    elif kwargs["target"] == "rtntype":
        node_rtntypes = NODE_DATA["rtntype"]
        splitted_rtntypes = node_rtntypes.parallel_apply(camel_case_split)
        splitted_rtntypes = [value for _, value in splitted_rtntypes.iteritems()]
        words_withdup = reduce(lambda acc, elem: acc+exclude_first_last(elem), splitted_rtntypes, [])
        words_withdup = list(map(lambda name: name.lower(), words_withdup))
        words_withdup = list(filter(lambda name: name not in JAVA_BUILTIN_TYPES and\
                                    name not in JAVA_BUILTIN_CLASSES,#and\
                                    # name not in JAVA_BUILTIN_COLLS and\
                                    # name not in JAVA_BUILTIN_UTILS,
                                    words_withdup))
        words_nodup = set(words_withdup)
        acc = []
        for name in words_nodup:
            acc.append((name, words_withdup.count(name)))
        return sorted(acc, key=lambda x: x[1], reverse=True)

    elif kwargs["target"] == "rtntype-suffix":
        node_rtntypes = NODE_DATA["rtntype"]
        splitted_rtntypes = node_rtntypes.parallel_apply(camel_case_split)
        splitted_rtntypes = [value for _, value in splitted_rtntypes.iteritems()]
        words_withdup = list(map(lambda elem: elem[len(elem)-1], splitted_rtntypes))
        words_withdup = list(filter(lambda name: name not in JAVA_BUILTIN_TYPES and\
                                    name not in JAVA_BUILTIN_CLASSES,#and\
                                    # name not in JAVA_BUILTIN_COLLS and\
                                    # name not in JAVA_BUILTIN_UTILS,
                                    words_withdup))
        words_nodup = set(words_withdup)
        acc = []
        for name in words_nodup:
            acc.append((name, words_withdup.count(name)))
        return sorted(acc, key=lambda x: x[1], reverse=True)

    elif kwargs["target"] == "classname-prefix":
        node_classnames = NODE_DATA["class"]
        splitted_classnames = node_classnames.parallel_apply(camel_case_split)
        splitted_classnames = [value for _, value in splitted_classnames.iteritems()]
        words_withdup = list(map(lambda elem: elem[0], splitted_classnames))
        words_withdup = list(filter(lambda name: name not in JAVA_BUILTIN_TYPES and\
                                    name not in JAVA_BUILTIN_CLASSES,#and\
                                    # name not in JAVA_BUILTIN_COLLS and\
                                    # name not in JAVA_BUILTIN_UTILS,
                                    words_withdup))
        words_nodup = set(words_withdup)
        acc = []
        for name in words_nodup:
            acc.append((name, words_withdup.count(name)))
        return sorted(acc, key=lambda x: x[1], reverse=True)

    elif kwargs["target"] == "classname":
        node_classnames = NODE_DATA["class"]
        splitted_classnames = node_classnames.parallel_apply(camel_case_split)
        splitted_classnames = [value for _, value in splitted_classnames.iteritems()]
        words_withdup = reduce(lambda acc, elem: acc+exclude_first_last(elem), splitted_classnames, [])
        words_withdup = list(map(lambda name: name.lower(), words_withdup))
        words_withdup = list(filter(lambda name: name not in JAVA_BUILTIN_TYPES and\
                                    name not in JAVA_BUILTIN_CLASSES,#and\
                                    # name not in JAVA_BUILTIN_COLLS and\
                                    # name not in JAVA_BUILTIN_UTILS,
                                    words_withdup))
        words_nodup = set(words_withdup)
        acc = []
        for name in words_nodup:
            acc.append((name, words_withdup.count(name)))
        return sorted(acc, key=lambda x: x[1], reverse=True)

    elif kwargs["target"] == "classname-suffix":
        node_classnames = NODE_DATA["class"]
        splitted_classnames = node_classnames.parallel_apply(camel_case_split)
        splitted_classnames = [value for _, value in splitted_classnames.iteritems()]
        words_withdup = list(map(lambda elem: elem[0], splitted_classnames))
        words_withdup = list(filter(lambda name: name not in JAVA_BUILTIN_TYPES and\
                                    name not in JAVA_BUILTIN_CLASSES,#and\
                                    # name not in JAVA_BUILTIN_COLLS and\
                                    # name not in JAVA_BUILTIN_UTILS,
                                    words_withdup))
        words_nodup = set(words_withdup)
        acc = []
        for name in words_nodup:
            acc.append((name, words_withdup.count(name)))
        return sorted(acc, key=lambda x: x[1], reverse=True)


def flatten(ll):
    return [elem for lst in ll for elem in lst]


def preprocess_intype(raw_intypes):
    acc = []
    for raw_intype in raw_intypes:
        if "," in raw_intype:
            acc += raw_intype.split(",")
        else:
            acc.append(raw_intype)
    return pd.Series(acc)


def find_frequents(**kwargs):
    if kwargs["target"] == "rtntype":
        node_rtntypes = NODE_DATA["rtntype"]
        node_rtntypes = node_rtntypes[~node_rtntypes.isin(JAVA_BUILTIN_TYPES) &
                                      # ~node_rtntypes.isin(JAVA_BUILTIN_COLLS) &
                                      # ~node_rtntypes.isin(JAVA_BUILTIN_UTILS) &
                                      ~node_rtntypes.isin(JAVA_BUILTIN_CLASSES)]
        counterobj = Counter(node_rtntypes)
        most_commons = counterobj.most_common(10)
        return sorted(most_commons, key=lambda x: x[1], reverse=True)

    elif kwargs["target"] == "intype":
        node_intypes = preprocess_intype(NODE_DATA["intype"])
        node_intypes = node_intypes[~node_intypes.isin(JAVA_BUILTIN_TYPES) &
                                    # ~node_intypes.isin(JAVA_BUILTIN_COLLS) &
                                    # ~node_intypes.isin(JAVA_BUILTIN_UTILS) &
                                    ~node_intypes.isin(JAVA_BUILTIN_CLASSES)]
        counterobj = Counter(node_intypes)
        most_commons = counterobj.most_common(10)
        return sorted(most_commons, key=lambda x: x[1], reverse=True)

    elif kwargs["target"] == "callees":
        top10 = CALLGRAPH.id1.value_counts().head(10)
        return list(top10.index)


# Parameters =============================
# ========================================


TOP_FREQ_N_NAME_PREFIXES = 10         # name 접두사의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_NAME_WORDS = 10            # name 낱말의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_RTNTYPE_PREFIXES = 10      # rtntype 접두사의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_RTNTYPE_WORDS = 10         # rtntype 낱말의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_RTNTYPE_SUFFIXES = 10      # rtntype의 접두사의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_CLASSNAME_PREFIXES = 10    # class 접두사의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_CLASSNAME_WORDS = 10       # class 낱말의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_CLASSNAME_SUFFIXES = 10    # class 낱말의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_RTNTYPES = 10              # rtntype을 통째로 생각했을 때, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_INTYPES = 10               # intypes 낱말의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_CALLEES = 10               # callee들의 경우, 상위 몇 순위까지 고려할 거냐?


# Constants ============================
# ======================================

TOP_FREQ_NAME_PREFIXES = list(map(lambda tup: tup[0],
                                  find_frequent_words(target="name-prefix")[:TOP_FREQ_N_NAME_PREFIXES]))

TOP_FREQ_NAME_WORDS = list(map(lambda tup: tup[0],
                               find_frequent_words(target="name")[:TOP_FREQ_N_NAME_WORDS]))

TOP_FREQ_RTNTYPE_WORDS = list(map(lambda tup: tup[0],
                                  find_frequent_words(target="rtntype")[:TOP_FREQ_N_RTNTYPE_WORDS]))

TOP_FREQ_CLASSNAME_WORDS = list(map(lambda tup: tup[0],
                                    find_frequent_words(target="classname")[:TOP_FREQ_N_CLASSNAME_WORDS]))

TOP_FREQ_CLASSNAME_SUFFIXES = list(map(lambda tup: tup[0],
                                    find_frequent_words(target="classname-suffix")[:TOP_FREQ_N_CLASSNAME_WORDS]))

TOP_FREQ_RTNTYPES = list(map(lambda tup: tup[0],
                             find_frequents(target="rtntype")[:TOP_FREQ_N_RTNTYPES]))

TOP_FREQ_INTYPES = list(map(lambda tup: tup[0],
                            find_frequents(target="intype")[:TOP_FREQ_N_INTYPES]))

TOP_FREQ_CALLEES = find_frequents(target="callees")[:TOP_FREQ_N_CALLEES]


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
    prefix = prefix.lower()
    out = dict()
    for freq_word in TOP_FREQ_NAME_PREFIXES:
        out[("method_name_starts_with", freq_word)] = prefix == freq_word
    return out    # key: word, val: boolean


def method_name_contains(node):
    """Does this method's name contain the given word?
       NOTE Higher-order feature"""
    words = camel_case_split(node[3])
    words = list(map(lambda string: string.lower(), words))
    out = dict()
    for freq_word in TOP_FREQ_NAME_WORDS:
        out[("method_name_contains", freq_word)] = freq_word in words
    return out    # key: word, val: boolean


def return_type_contains_name(node):
    """Does the return type contain the given name?
       NOTE Higher-order feature"""
    words = camel_case_split(node[2])
    words = list(map(lambda string: string.lower(), words))
    out = dict()
    for freq_word in TOP_FREQ_RTNTYPE_WORDS:
        out[("return_type_contains_name", freq_word)] = freq_word in words
    return out    # key: word, val: boolean
    out = dict()
    for freq_word in TOP_FREQ_CLASSNAME_WORDS:
        out[("class_contains_name", freq_word)] = freq_word in words
    return out    # key: word, val: boolean


def class_endswith_name(node):
    """Is the method part of class that ends with the given name?
       NOTE Higher-order feature"""
    words = camel_case_split(node[1])
    words = list(map(lambda string: string.lower(), words))
    suffix = camel_case_split(node[1])[len(words)-1]
    out = dict()
    for freq_word in TOP_FREQ_CLASSNAME_SUFFIXES:
        out[("class_endswith_name", freq_word)] = suffix == freq_word
    return out


def rtntype_equals(node):
    """Is the return type of the method equal to the type given?
       NOTE Higher-order feature"""
    rtntype = node[2]
    out = dict()
    for freq_rtntype in TOP_FREQ_RTNTYPES:
        out[("returntype_equals", freq_rtntype)] = rtntype == freq_rtntype
    return out


def param_contains_type_or_name(node):
    """Do any of the parameters' type contain the given name?
       NOTE Higher-order feature"""
    intypes = node[4].split(",")
    out = dict()
    for freq_intype in TOP_FREQ_INTYPES:
        out[("param_contains_type_or_name", freq_intype)] =\
            reduce(lambda acc, elem: elem == freq_intype or acc, intypes, False)
    return out


def param_type_matches_return_type(node):
    """Does any of the parameters match the return type?"""
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
    rtntype = node[2].lower()
    methname = node[3]
    return rtntype in list(map(lambda string: string.lower(),
                               camel_case_split(methname)))


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


def handle_multiindex_higherorder(df):
    keys = list(df.iloc[0].keys())
    df = pd.DataFrame(df, columns=["original"])
    df = df.apply(lambda row: row["original"].values(), result_type="expand", axis=1)
    df.columns = pd.MultiIndex.from_tuples(keys)
    return df


def apply_and_concat():
    """parallel apply to NODE_DATA and concat them altogether"""
    id_df = pd.DataFrame(NODE_DATA['id'], columns=pd.MultiIndex.from_tuples([("id", "")]))

    # raw applied dataframes: before handling columns
    has_parameters_df = NODE_DATA.parallel_apply(has_parameters, axis=1)
    has_return_type_df = NODE_DATA.parallel_apply(has_return_type, axis=1)
    method_name_starts_with_df = NODE_DATA.parallel_apply(method_name_starts_with, axis=1)
    method_name_contains_df = NODE_DATA.parallel_apply(method_name_contains, axis=1)
    return_type_contains_name_df = NODE_DATA.parallel_apply(return_type_contains_name, axis=1)
    class_contains_name_df = NODE_DATA.parallel_apply(class_contains_name, axis=1)
    class_endswith_name_df = NODE_DATA.parallel_apply(class_endswith_name, axis=1)
    rtntype_equals_df = NODE_DATA.parallel_apply(rtntype_equals, axis=1)
    param_contains_type_or_name_df = NODE_DATA.parallel_apply(param_contains_type_or_name, axis=1)
    param_type_matches_return_type_df = NODE_DATA.parallel_apply(param_type_matches_return_type, axis=1)
    is_real_setter_df = NODE_DATA.parallel_apply(is_real_setter, axis=1)
    void_on_method_df = NODE_DATA.parallel_apply(void_on_method, axis=1)
    method_name_contains_return_type_df = NODE_DATA.parallel_apply(method_name_contains_return_type, axis=1)
    invocation_name_df = NODE_DATA.parallel_apply(invocation_name, axis=1)
    calling_but_no_df_df = NODE_DATA.parallel_apply(calling_but_no_df, axis=1)
    called_but_no_df_df = NODE_DATA.parallel_apply(called_but_no_df, axis=1)
    making_df_call_df = NODE_DATA.parallel_apply(making_df_call, axis=1)
    has_df_call_df = NODE_DATA.parallel_apply(has_df_call, axis=1)
    receiving_and_passing_data_df = NODE_DATA.parallel_apply(receiving_and_passing_data, axis=1)
    has_df_call_and_dead_df = NODE_DATA.parallel_apply(has_df_call_and_dead, axis=1)
    has_redefine_df = NODE_DATA.parallel_apply(has_redefine, axis=1)

    # multi-index first-order features
    has_parameters_df = pd.DataFrame(has_parameters_df,
                                     columns=pd.MultiIndex.from_tuples([("has_parameters", "")]))
    has_return_type_df = pd.DataFrame(has_parameters_df,
                                      columns=pd.MultiIndex.from_tuples([("has_return_type", "")]))
    param_type_matches_return_type_df = pd.DataFrame(param_type_matches_return_type_df,
                                                     columns=pd.MultiIndex.from_tuples([("param_type_matches_return_type", "")]))
    is_real_setter_df = pd.DataFrame(is_real_setter_df,
                                     columns=pd.MultiIndex.from_tuples([("is_real_setter", "")]))
    void_on_method_df = pd.DataFrame(void_on_method_df,
                                     columns=pd.MultiIndex.from_tuples([("void_on_method", "")]))
    method_name_contains_return_type_df = pd.DataFrame(method_name_contains_return_type_df,
                                                               columns=pd.MultiIndex.from_tuples([("method_name_contains_return_type", "")]))
    calling_but_no_df_df = pd.DataFrame(calling_but_no_df_df,
                                        columns=pd.MultiIndex.from_tuples([("calling_but_no_df", "")]))
    called_but_no_df_df = pd.DataFrame(called_but_no_df_df,
                                       columns=pd.MultiIndex.from_tuples([("called_but_no_df", "")]))
    making_df_call_df = pd.DataFrame(making_df_call_df,
                                     columns=pd.MultiIndex.from_tuples([("making_df_call", "")]))
    has_df_call_df = pd.DataFrame(has_df_call_df,
                                  columns=pd.MultiIndex.from_tuples([("has_df_call", "")]))
    receiving_and_passing_data_df = pd.DataFrame(receiving_and_passing_data_df,
                                                 columns=pd.MultiIndex.from_tuples([("receiving_and_passing_data", "")]))
    has_df_call_and_dead_df = pd.DataFrame(has_df_call_and_dead_df,
                                           columns=pd.MultiIndex.from_tuples([("has_df_call_and_dead", "")]))
    has_redefine_df = pd.DataFrame(has_redefine_df,
                                   columns=pd.MultiIndex.from_tuples([("has_redefine", "")]))

    # multi-index higher-order features
    method_name_contains_df = handle_multiindex_higherorder(method_name_contains_df)
    method_name_starts_with_df = handle_multiindex_higherorder(method_name_starts_with_df)
    return_type_contains_name_df = handle_multiindex_higherorder(return_type_contains_name_df)
    class_contains_name_df = handle_multiindex_higherorder(class_contains_name_df)
    class_endswith_name_df = handle_multiindex_higherorder(class_endswith_name_df)
    rtntype_equals_df = handle_multiindex_higherorder(rtntype_equals_df)
    param_contains_type_or_name_df = handle_multiindex_higherorder(param_contains_type_or_name_df)
    invocation_name_df = handle_multiindex_higherorder(invocation_name_df)

    return pd.concat([ id_df,
                       has_parameters_df,
                       has_return_type_df,
                       method_name_starts_with_df,
                       method_name_contains_df,
                       return_type_contains_name_df,
                       class_contains_name_df,
                       class_endswith_name_df,
                       rtntype_equals_df,
                       param_contains_type_or_name_df,
                       param_type_matches_return_type_df,
                       is_real_setter_df,
                       void_on_method_df,
                       method_name_contains_return_type_df,
                       invocation_name_df,
                       calling_but_no_df_df,
                       called_but_no_df_df,
                       making_df_call_df,
                       has_df_call_df,
                       receiving_and_passing_data_df,
                       has_df_call_and_dead_df,
                       has_redefine_df ], axis=1)

# Visualization Utilities ============
# ====================================

def get_count_of_column(feature_vectors, colname):
    """한 column의 value의 분포를 pie chart로 visualize한다.
       parameter col의 input type: String"""
    # getting the proportion of Feature Values
    counts = feature_vectors[colname].value_counts()
    True_cnt = counts.get(True)
    False_cnt = counts.get(False)
    if True_cnt is None:
        True_cnt = 0
    if False_cnt is None:
        False_cnt = 0

    return True_cnt, False_cnt


def visualize_single_page(feature_vectors, colnames):
    """Visualize a single page with a given chunk of
       25 columns."""
    f, axes = plt.subplots(5, 5)
    colnames = iter(colnames)

    for i in range(5):
        for j in range(5):
            try:
                colname = next(colnames)
            except:
                return
            axes[i, j].set_title(colname)
            True_cnt, False_cnt = get_count_of_column(feature_vectors, colname)
            # Parameters to .pie()
            group_sizes = [True_cnt, False_cnt]
            group_names = ["True", "False"]
            group_colors = []
            group_explodes = (0.1, 0)  # separate 1st slice
            axes[i, j].pie(group_sizes,
                           explode=group_explodes,
                           labels=group_names,
                           # autopct='%1.2f%%',
                           shadow=True,
                           startangle=90,
                           textprops={'fontsize': 7})
            # visualize the 25 subplots!
    plt.tight_layout()
    plt.show()


def visualize_all_columns(feature_vectors):
    # indices to place subplots
    # need to define a zipped list of colnames and page_nums
    acc = []                    # may change name
    colnames = list(feature_vectors.columns)[1:]
    for i in range(7):
        acc += list(repeat(i, 25))
        colnames_and_pagenums = list(zip(colnames, acc))

    # now, partition these by pagenums
    acc = []
    for i in range(7):
        partition = list(filter(lambda tup: tup[1] == i, colnames_and_pagenums))
        acc.append(partition)
        column_chunks = list(map(lambda lst: list(map(lambda tup: tup[0], lst)), acc))
    for column_chunk in column_chunks:
        visualize_single_page(feature_vectors, column_chunk)


def get_TrueFalse_ratio_one_column(colname):
    """Get the proportion of True values for a single column"""
    True_cnt, False_cnt = get_count_of_column(colname)
    return 0 if True_cnt == False_cnt == 0 else True_cnt / (True_cnt + False_cnt)


def get_TrueFalse_ratio_all_columns(feature_vectors):
    """Get the proportion of True values for all columns and print it"""
    colnames = list(feature_vectors.columns)[1:]
    for colname in colnames:
        ratio = get_TrueFalse_ratio_one_column(colname)
        print(colname, ":", ratio)


# main ================================
# =====================================


def main():
    feature_vectors = apply_and_concat()
    feature_vectors.to_csv("feature_vectors.csv", mode="w+")


if __name__ == "__main__":
    main()
