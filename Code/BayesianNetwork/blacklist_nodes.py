import os
import os.path
import glob

# parameterizable
PROJECT_ROOT = os.path.join('..', 'benchmarks', 'realworld', 'sagan')

def create_blacklist():
    whitelist, blacklist = [], []
    for current_dir, directories, files in os.walk(PROJECT_ROOT):
        if 'tests' in current_dir or 'test' in current_dir:
            blacklist += glob.glob(os.path.join(current_dir, "*.java"))
        else:
            whitelist += glob.glob(os.path.join(current_dir, "*.java"))
    return whitelist, blacklist


def main():
    whitelist, blacklist = create_blacklist()
