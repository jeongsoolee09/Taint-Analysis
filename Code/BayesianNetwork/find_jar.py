# .jar 파일이 있는 toplevel 경로를 찾아낸다.
# split_underlying_graph의 dependency.

import os
import os.path
import glob
import json


def retrieve_path():
    """paths.json을 읽고 path를 가져온다."""
    with open("paths.json", "r+") as pathjson:
        pathdict = json.load(pathjson)
    return pathdict["project_root_directory"]


PROJECT_ROOT = retrieve_path()


def find_jar_paths(project_root):
    jar_files = []
    for current_dir, directories, files in os.walk(project_root):
        if "test" in current_dir:
            continue
        jar_files += glob.glob(os.path.join(current_dir, "*.jar"))
    return jar_files


def take_jar_dir(jar_files):
    """*.jar를 가리키는 full directory 중에서 sagan의 한 단계 밑까지만 남기기.
       e.g. ../benchmarks/realworld/sagan/sagan-renderer/build/libs의 경우,
            ../benchmarks/realworld/sagan/sagan-renderer를 리턴."""
    splitted_paths = jar_files.split(os.sep)
    splitted_paths.reverse()
    current_dir = ""
    while current_dir != PROJECT_ROOT:
        current_dir += splitted_paths.pop()
        if current_dir == splitted_paths:
            break
        current_dir += os.sep
    current_dir += splitted_paths.pop()
    return current_dir


def has_java_file(directory):
    """directory tree를 walk할 때 .java 파일이 있는지를 판단하는 predicate"""
    java_files = []
    for current_dir, directories, files in os.walk(directory):
        if "test" in current_dir:
            continue
        java_files += glob.glob(os.path.join(current_dir, "*.java"))
    return java_files != []


def real_jar_paths(project_root):
    """.jar로 컴파일되는 path의 목록을 찾아 낸다."""
    all_jar_full_paths = find_jar_paths(project_root)
    all_jar_paths = list(map(take_jar_dir, all_jar_full_paths))
    return list(filter(has_java_file, all_jar_paths))
