# Feature extractor based on ISSTA'19
import modin.pandas as pd

# Constants ============================
# ======================================

NODE_NAMES = pd.read_csv("nodes.csv", index_col=0)

# Utility Funcs ========================
# ======================================

def camel_case_into_stringlist(string):
    """split the camel case string into words, and undercase those words"""
    pass


def find_frequent_words():
    pass

# Feature Extractors =====================
# ========================================

# the parameter "node" stands for a row in NODE_NAMES

def method_name_starts_with(node):
    return some boolean list


def method_name_equals(node):
    return some boolean list


def method_name_contains(node):
    return some boolean list


def has_parameters(node):
    return node.intype != "void"


def has_return_type(node):
    return node.rtntype != "void"


def return_type_contains_name(node):
    return some boolean list


# Batch run ==========================
# ====================================

def run_all_extractors(node):
    """batch run the feature extractors on a method"""
    pass


# main ================================
# =====================================


def main():
    # batch run the feature extractors on all methods (or maybe we can use modin.pandas.apply)
    for node_name in NODE_NAMES:
        pass
    # and then write to csv
