# Feature extractor based on ISSTA'19
import modin.pandas as pd
import re
from functools import reduce

# Utility Funcs ========================
# ======================================

# https://stackoverflow.com/questions/29916065/how-to-do-camelcase-split-in-python
def camel_case_split(identifier):
    matches = re.finditer('.+?(?:(?<=[a-z])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])|$)', identifier)
    return [m.group(0) for m in matches]

# Constants ============================
# ======================================

with open("java_builtin_types.txt", "r+") as builtintypes:
    JAVA_BUILTIN_TYPES = list(map(lambda string: string.rstrip(), builtintypes.readlines()))


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

# More Constants =======================
# ======================================

NODE_DATA = pd.read_csv("nodes.csv", index_col=0)
TOP_FREQ_N_NAME = 10  # 상위 몇 순위까지 할 거냐?
TOP_FREQ_NAME_WORDS = list(map(lambda tup: tup[0], find_frequent_words(target="name")[:TOP_FREQ_N_NAME]))
TOP_FREQ_N_RTNTYPE = 10
TOP_FREQ_RTNTYPE_WORDS = list(map(lambda tup: tup[0],
                                  find_frequent_words(target="rtntype")[:TOP_FREQ_N_RTNTYPE]))

# Feature Extractors =====================
# ========================================

# the parameter "node" stands for a row in NODE_DATA

# F06
def has_parameters(node):
    return node.intype != "void"


# F07
def has_return_type(node):
    return node.rtntype != "void"


# F14
def method_name_starts_with(node):
    prefix = camel_case_split(node.name)[0]
    out = dict()
    for freq_word in TOP_FREQ_NAME_WORDS:
        out[("F14", freq_word)] = prefix == freq_word
    return out    # key: word, val: boolean


# F15
def method_name_equals(node):
    out = dict()
    for freq_word in TOP_FREQ_NAME_WORDS:
        out[("F15", freq_word)] = freq_word == node.name
    return out    # key: word, val: boolean


# F16
def method_name_contains(node):
    words = camel_case_split(node.name)
    out = dict()
    for freq_word in TOP_FREQ_NAME_WORDS:
        out[("F16", freq_word)] = freq_word in words
    return out    # key: word, val: boolean


# F22
def return_type_contains_name(node):
    words = camel_case_split(node.rtntype)
    out = dict()
    for freq_word in TOP_FREQ_NAME_WORDS:
        out[("F22", freq_word)] = freq_word in words
    return out    # key: word, val: boolean

# Batch run ==========================
# ====================================

def run_all_extractors(node):
    """batch run the feature extractors on a method"""
    F06 = has_parameters(node)  # bool: 바로 append
    F07 = has_return_type(node)  # bool: 바로 append
    F14 = method_name_starts_with(node)  # dict: pd.dataframe
    F15 = method_name_equals(node)       # dict: pd.dataframe
    F16 = method_name_contains(node)     # dict: pd.dataframe
    F22 = return_type_contain_name(node)  # dict: pd.dataframe
    
    F15_df = pd.DataFrame(F15, index=[0])
    F16_df = pd.DataFrame(F16, index=[0])
    F22_df = pd.DataFrame(F22, index=[0])
    
    vector = pd.concat([F15_df, F16_df, F22_df], axis=1)

    return vector

# main ================================
# =====================================


def main():
    # batch run the feature extractors on all methods (or maybe we can use modin.pandas.apply)
    # and then write to csv
    pass
