# Feature extractor based on ISSTA'19: Codebase-Adaptive Detection of Security-Relevant Methods (a.k.a. SWAN)
import modin.pandas as pd
import re
from functools import reduce
import collections

# Utility Funcs ========================
# ======================================

NODE_DATA = pd.read_csv("nodes.csv", index_col=0)

# https://stackoverflow.com/questions/29916065/how-to-do-camelcase-split-in-python
def camel_case_split(identifier):
    matches = re.finditer('.+?(?:(?<=[a-z])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])|$)', identifier)
    return [m.group(0) for m in matches]


def find_frequent_words(**kwargs):
    """available kwargs:
       - target: 'name', 'rtntype'"""
    if kwargs["target"] == 'name':
        node_names = NODE_DATA[kwargs["target"]]
        splitted_names = node_names.apply(camel_case_split, axis=1)
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
        splitted_rtntypes = node_rtntypes.apply(camel_case_split, axis=1)
        splitted_rtntypes = [value for _, value in splitted_rtntypes.iteritems()]
        words_withdup = reduce(lambda acc, elem: acc+elem, splitted_rtntypes, [])
        words_withdup = list(map(lambda name: name.lower(), words_withdup))
        words_withdup = list(filter(lambda name: name not in JAVA_BUILTIN_TYPES, words_withdup))
        words_nodup = set(words_withdup)
        acc = []
        for name in words_nodup:
            acc.append((name, words_withdup.count(name)))
        return sorted(acc, key=lambda x: x[1], reverse=True)


def find_frequents(**kwargs):
    if kwargs["target"] == "rtntype":
        node_rtntypes = NODE_DATA[kwargs["target"]]
        counterobj = collections.Counter(node_rtntypes)
        most_commons = counterobj.most_common(10)
        return sorted(most_commons, key=lambda x: x[1], reverse=True)

# Parameters =============================
# ========================================


TOP_FREQ_N_NAME_WORDS = 10            # name 낱말의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_RTNTYPE_WORDS = 10         # rtntype 낱말의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_CLASSNAME_WORDS = 10       # class 낱말의 경우, 상위 몇 순위까지 고려할 거냐?
TOP_FREQ_N_RTNTYPES = 10              # rtntype을 통째로 생각했을 때, 상위 몇 순위까지 고려할 거냐?

# Constants ============================
# ======================================


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

# Feature Extractors =====================
# ========================================
# the parameter "node" stands for a row in NODE_DATA

# F06
def has_parameters(node):
    return node.intype != "void"


# F07
def has_return_type(node):
    return node.rtntype != "void"


# F10
def method_name_starts_with(node):
    prefix = camel_case_split(node[3])[0]
    out = dict()
    for freq_word in TOP_FREQ_NAME_WORDS:
        out[("F10", freq_word)] = prefix == freq_word
    return out    # key: word, val: boolean


# F12
def method_name_contains(node):
    words = camel_case_split(node[3])
    out = dict()
    for freq_word in TOP_FREQ_NAME_WORDS:
        out[("F12", freq_word)] = freq_word in words
    return out    # key: word, val: boolean


# F18
def return_type_contains_name(node):
    words = camel_case_split(node[2])
    out = dict()
    for freq_word in TOP_FREQ_RTNTYPE_WORDS:
        out[("F18", freq_word)] = freq_word in words
    return out    # key: word, val: boolean


# F03
def class_contains_name(node):
    words = camel_case_split(node[1])
    out = dict()
    for freq_word in TOP_FREQ_CLASSNAME_WORDS:
        out[("F03", freq_word)] = freq_word in words
    return out    # key: word, val: boolean


# F04
def class_endswith_name(node):
    words = camel_case_split(node[1])
    suffix = camel_case_split(node[1])[len(words)-1]
    out = dict()
    for freq_word in TOP_FREQ_CLASSNAME_WORDS:
        out[("F04", freq_word)] = suffix == freq_word
    return out


# F23
def rtntype_equals(node):
    rtntype = node[2]
    out = dict()
    for freq_rtntype in TOP_FREQ_RTNTYPES:
        out[("F23", "")] = rtntype == freq_rtntype
    return out


# F17
def intype_matches_rtntype(node):
    intype = node[4]
    rtntype = node[2]
    return intype == rtntype


# Batch run ==========================
# ====================================

def run_all_extractors(node_row):
    """batch run the feature extractors on a method"""
    node_id = [node_row[5]]  # the id of the method
    id_df = pd.DataFrame([node_id], columns=pd.MultiIndex.from_tuples([("id", "")]))

    F06 = has_parameters(node_row)  # bool
    F06_df = pd.DataFrame([F06], columns=pd.MultiIndex.from_tuples([("F06", "")]))

    F07 = has_return_type(node_row)  # bool
    F07_df = pd.DataFrame([F07], columns=pd.MultiIndex.from_tuples([("F07", "")]))

    F10 = method_name_starts_with(node_row)  # dict
    F10_df = pd.DataFrame(F10, index=[0])

    F12 = method_name_contains(node_row)     # dict
    F12_df = pd.DataFrame(F12, index=[0])

    F18 = return_type_contains_name(node_row)  # dict
    F18_df = pd.DataFrame(F18, index=[0])

    vector = pd.concat([id_df, F06_df, F07_df, F10_df, F12_df, F18_df], axis=1)

    return vector

# main ================================
# =====================================


def main():
    sim_df = pd.DataFrame()
    for tup in NODE_DATA.itertuples(index=False):  # 크기가 작으니까 가능한 거다
        vector = run_all_extractors(tup)
        sim_df = pd.concat([sim_df, vector])
    sim_df.to_csv("sim_vectors.csv", mode="w+")

