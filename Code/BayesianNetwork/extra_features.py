# BN edge formation을 위해 Pairwise Similarity를 결정하기 위한 feature 값을 정해 주는 모듈이 아닌,
# tabula_non_rasa에서 tentative rule을 적용하기 위한 feature 값을 정해 주는 모듈.
# 하나의 그래프에 대해서만 dataframe을 그린다.

import json
import pandas as pd
import networkx as nx
import re

from create_node import process

def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]


# Constants ================================
# ==========================================

PROJECT_ROOT_DIR = retrieve_path()

with open(os.path.join(PROJECT_ROOT_DIR, "GetterSetter.json"), "r+") as f:
    GETTER_SETTER = json.load(f)

with open("java_builtin_types.txt", "r+") as f:
    builtin_type_classes = f.readlines()
    builtin_type_classes = list(map(lambda x: x.rstrip(), builtin_type_classes))
    builtin_type_classes = list(filter(lambda x:\
                                 '[' not in x and
                                 ']' not in x, builtin_type_classes))
    wrapped_primitives = list(map(lambda string: string[0].upper() + string[1:], builtin_type_classes))


with open("java_builtin_collections.txt", "r+") as f:
    builtin_collections = f.readlines()
    builtin_collections = list(map(lambda x: x.rstrip(), builtin_collections))

# feature value setters ========================
# ==============================================

def getter_setter_mapfunc(row):
    try:
        return GETTER_SETTER[row["name"]]
    except:
        return "nothing"


def set_getter_setter(df):
    """getter_setter 칼럼의 값을 ['getter'|'setter'|'nothing']으로 초기화"""
    getter_setter_val_df = df.apply(getter_setter_mapfunc, axis=1)
    df["getter_setter"] = getter_setter_val_df
    return df


# https://stackoverflow.com/questions/29916065/how-to-do-camelcase-split-in-python
def camel_case_split(identifier):
    matches = re.finditer('.+?(?:(?<=[a-z])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])|$)', identifier)
    return [m.group(0) for m in matches]


def is_hashCode_mapfunc(row):
    if "hashCode" == process(row['name'])[2]:
        return True
    else:
        return False


def is_assert_mapfunc(row):
    if "assert" in camel_case_split(row["name"]): 
        return True
    else:
        return False


def set_is_hashCode(df):
    """is_hashCode 칼럼의 값을 [True|False]로 초기화"""
    is_hashCode_val_df = df.apply(is_hashCode_mapfunc, axis=1)
    df["is_hashCode"] = is_hashCode_val_df
    return df


def set_is_assert(df):
    """is_assert 칼럼의 값을 [True|False]로 초기화"""
    is_assert_val_df = df.apply(is_assert_mapfunc, axis=1)
    df["is_assert"] = is_assert_val_df
    return df


def is_to_mapfunc(row):
    if camel_case_split(row["name"])[0] == "to": 
        return True
    else:
        return False


def set_is_to(df):
    """is_to 칼럼의 값을 [True|False]로 초기화"""
    is_to_val_df = df.apply(is_assert_mapfunc, axis=1)
    df["is_to"] = is_to_val_df
    return df


def is_wrapping_primitive_mapfunc(row):
    classname = process(row['name'])[0]
    if classname in wrapped_primitives:
        return True
    else:
        return False


def set_is_wrapping_primitive(df):
    """is_wrapping_primitive 칼럼의 값을 [True|False]로 초기화"""
    is_wrapping_primitive_val_df = df.apply(is_wrapping_primitive_mapfunc, axis=1)
    df["is_wrapping_primitive"] = is_wrapping_primitive_val_df
    return df


def is_builtin_coll_mapfunc(row):
    classname = process(row['name'])[0]
    if classname in builtin_collections:
        return True
    else:
        return False


def set_is_builtin_coll(df):
    """is_builtin_coll 칼럼의 값을 [True|False]로 초기화"""
    is_builtin_coll_df = df.apply(is_builtin_coll_mapfunc, axis=1)
    df["is_builtin_coll"] = is_builtin_coll_df
    return df


# main =================================
# ======================================

def main(graph_file_name):
    """주어진 그래프에 대한 DataFrame을 초기화한다."""
    # name 칼럼에 들어갈 노드 이름들을 가져온다.
    graph = nx.read_gpickle(graph_file_name)
    node_names = list(graph.nodes)
    
    # "name" columns부터 만든다.
    df = pd.DataFrame(node_names, columns=['name'])

    # "getter_setter" column을 만든다.
    df = set_getter_setter(df)

    # "is_hashCode" column을 만든다.
    df = set_is_hashCode(df)

    # "is_assert" column을 만든다.
    df = set_is_assert(df)

    # "is_to" column을 만든다.
    df = set_is_to(df)

    # "is_wrapping_primitive" column을 만든다.
    df = set_is_wrapping_primitive(df)
    
    # "is_builtin_coll" column을 만든다.
    df = set_is_builtin_coll(df)

    df.to_csv("extra_features.csv", mode="w+")
