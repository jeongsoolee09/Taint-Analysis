import os

with open("Methods.txt", "r+") as f:
    lines = f.readlines()
    lines = list(map(lambda s: s.strip(), lines))

pure_methods = list(filter(lambda s: "<init>" not in s and "<clinit>" not in s, lines))

print(f"The number of pure methods is {len(pure_methods)}.")

file_acc = []
for _, _, files in os.walk("/Users/jslee/Taint-Analysis/Code/benchmarks/realworld/sagan/sagan-renderer"):
    file_acc += files
only_java_src = list(filter(lambda filename: ".java" in filename and "Test" not in filename, file_acc))

java_classnames = list(map(lambda filename: filename[:-5], only_java_src))


renderer_method_acc = []

for pure_method in pure_methods: 
    for java_classname in java_classnames:
        if java_classname in pure_method and "Test" not in pure_method and "lambda" not in pure_method and "Lambda" not in pure_method:
            renderer_method_acc.append(pure_method)

print(f"The number of methods in sagan-renderer is {len(renderer_method_acc )}.")
