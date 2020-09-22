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


def find_frequent_words():
    node_names = NODE_DATA["name"]  # 원본이랑 구조를 공유 안함: 새로운 카피를 만듦
    splitted_names = node_names.apply(camel_case_split, axis=1)
    splitted_names = [value for _, value in splitted_names.iteritems()]
    words_withdup = reduce(lambda acc, elem: acc+elem, splitted_names, [])
    words_withdup = list(map(lambda name: name.lower(), words_withdup))
    words_nodup = set(words_withdup)
    acc = []
    for name in words_nodup:
        acc.append((name, words_withdup.count(name)))
    return sorted(acc, key=lambda x: x[1], reverse=True)

# Constants ============================
# ======================================

NODE_DATA = pd.read_csv("nodes.csv", index_col=0)
TOP_FREQ_N = 10  # 상위 몇 순위까지 할 거냐?
TOP_FREQS = list(map(lambda tup: tup[0], find_frequent_words()[:TOP_FREQ_N]))

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
    return some boolean dict    # key: word, val: boolean


# F15
def method_name_equals(node):
    return some boolean dict    # key: word, val: boolean


# F16
def method_name_contains(node):
    TOP_FREQS
    return some boolean dict    # key: word, val: boolean


# F22
def return_type_contains_name(node):
    TOP_FREQS
    return some boolean dict    # key: word, val: boolean


# Batch run ==========================
# ====================================

def run_all_extractors(node):
    """batch run the feature extractors on a method"""
    pass


# main ================================
# =====================================


def main():
    # batch run the feature extractors on all methods (or maybe we can use modin.pandas.apply)
    for node_name in NODE_DATA:
        pass
    # and then write to csv
