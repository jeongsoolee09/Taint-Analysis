import os
import os.path
import glob

# parameterizable
PROJECT_ROOT = os.path.join('..', 'benchmarks', 'realworld', 'sagan')

def create_whitelist_blacklist():
    """주석"""
    whitelist_files, blacklist_files = [], []
    for current_dir, directories, files in os.walk(PROJECT_ROOT):
        if 'tests' in current_dir or 'test' in current_dir:
            blacklist_files += glob.glob(os.path.join(current_dir, "*.java"))
        else:
            whitelist_files += glob.glob(os.path.join(current_dir, "*.java"))
    return whitelist_files, blacklist_files


def extract_filename(path):
    """path에서 (확장자를 제외한) filename만을 추출한다."""
    _, tail = os.path.split(path)
    return tail.split('.')[0]


def main():
    whitelist_files, blacklist_files = create_whitelist_blacklist()
    whitelist = list(map(extract_filename, whitelist_files))
    blacklist = list(map(extract_filename, blacklist_files))
    return whitelist, blacklist
