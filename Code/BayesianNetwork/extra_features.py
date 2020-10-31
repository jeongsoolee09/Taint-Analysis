# BN edge formation을 위해 Pairwise Similarity를 결정하기 위한 feature 값을 정해 주는 모듈이 아닌,
# tabula_non_rasa에서 tentative rule을 적용하기 위한 feature 값을 정해 주는 모듈.
# 하나의 그래프에 대해서만 dataframe을 그린다.

import json
import modin.pandas as pd
import networkx as nx

# Constants ================================
# ==========================================

def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]


PROJECT_ROOT_DIR = retrieve_path()

with open(os.path.join(PROJECT_ROOT_DIR, "GetterSetter.json"), "r+") as f:
    GETTER_SETTER = json.load(f)


# feature value setters ========================
# ==============================================


def set_getter_setter(df):
    """getter_setter 칼럼의 값을 [getter|setter|nothing]으로 초기화"""
    # df["getter_setter"] =
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
