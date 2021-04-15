import json

# change this variable as needed
skip_func_path = "/Users/jslee/Taint-Analysis/Code/benchmarks/realworld/FFI/kafka-rest/skip_func.txt"

with open(skip_func_path, "r+") as f:
    skip_funcs = f.readlines()
    skip_funcs = list(map(lambda string: string.rstrip(), skip_funcs))

out = {}

for skip_func in skip_funcs:
    if "<init>" in skip_func or\
       "__" in skip_func:
        continue
    else:
        out[skip_func] = ""

with open("solution_kafka_rest.json", "w+") as f:
    json.dump(out, f, indent=4)
