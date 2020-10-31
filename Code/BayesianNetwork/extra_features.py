# BN edge formation을 위해 Pairwise Similarity를 결정하기 위한 feature 값을 정해 주는 모듈이 아닌,
# tabula_non_rasa에서 tentative rule을 적용하기 위한 feature 값을 정해 주는 모듈.
# 하나의 그래프에 대해서만 dataframe을 그린다.

import json
import modin.pandas as pd
import networkx as nx


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


# feature value setters ========================
# ==============================================

def getter_setter_mapfunc(row):
    try:
        return GETTER_SETTER[row["name"]]
    except:
        return "nothing"


# https://stackoverflow.com/questions/29916065/how-to-do-camelcase-split-in-python
def camel_case_split(identifier):
    matches = re.finditer('.+?(?:(?<=[a-z])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])|$)', identifier)
    return [m.group(0) for m in matches]


def set_getter_setter(df):
    """getter_setter 칼럼의 값을 [getter|setter|nothing]으로 초기화"""
    # 1. df에 들어 있는 각 node name을 GETTER_SETTER에서 찾아내고
    # 2. 해당되는 GETTER_SETTER의 value값을 그 row의 "getter_setter" 칼럼 값으로 한다.
    getter_setter_val_df = df.apply(getter_setter_mapfunc, axis=1)
    df["getter_setter"] = getter_setter_val_df
    return df


def set_is_assert(df):
    return df


def set_is_to(df):
    return df


def set_is_wrapping_primitive(df):
    return df


def set_is_builtin_coll(df):
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
    return df
