# pick_training_set : quantity * diversity -> dataset
# picks dataset from sagan (for now)

import json
import argparse
import random

# Getting the command line args

parser = argparse.ArgumentParser(description='Create dataset json by diversity and quantity.')
parser.add_argument('quantity', type=int, help='choose btw [52, 100, 152, 200]')
parser.add_argument('diversity', type=str, help='choose btw [more_src, more_sin, more_san, more_non, fair]')
args = parser.parse_args()

# Constants ============================================
# ======================================================

QUANTITY = args.quantity
DIVERSITY = args.diversity

MORE_SRC_52  = [40, 4, 4, 4]
MORE_SRC_100 = [75, 5, 5, 5]
MORE_SRC_152 = [113, 13, 13, 13]
MORE_SRC_200 = [149, 17, 17, 17]

MORE_SIN_52  = [4, 40, 4, 4]
MORE_SIN_100 = [5, 75, 5, 5]
MORE_SIN_152 = [17, 10, 17, 17]
MORE_SIN_200 = [33, 101, 33, 33]

MORE_SAN_52  = [4, 4, 40, 4]
MORE_SAN_100 = [10, 10, 70, 10]
MORE_SAN_152 = [27, 27, 71, 27]
MORE_SAN_200 = [43, 43, 71, 43]

MORE_NON_52  = [4, 4, 4, 40]
MORE_NON_100 = [5, 5, 5, 75]
MORE_NON_152 = [13, 13, 13, 113]
MORE_NON_200 = [17, 17, 17, 149]

FAIR_52  = [13, 13, 13, 13]
FAIR_100 = [25, 25, 25, 25]
FAIR_152 = [38, 38, 38, 38]
FAIR_200 = [50, 50, 50, 50]

# Methods ==============================================
# ======================================================

def swanify_name(solution_slice):
    meth_id = solution_slice[0]
    meth_id = meth_id.split(" ")[1]  # remove rtntype
    meth_id = meth_id.split("(")[0]  # remove arglist
    return meth_id


def swanify_return(solution_slice):
    meth_id = solution_slice[0]
    rtntype = meth_id.split(" ")[0]
    # 일단 패키지는 생략
    return rtntype


def swanify_parameters(solution_slice):
    acc = []
    meth_id = solution_slice[0]
    arglist_str = meth_id.split("(")[1]
    arglist = arglist_str.rstrip(")").split(",")
    return arglist


def swanify_dataIn(solution_slice):
    parameters = swanify_parameters(solution_slice)
    return {"return": False, "parameters": [x for x in range(len(parameters))]}


def swanify_dataOut(solution_slice):
    parameters = swanify_parameters(solution_slice)
    return {"return": parameters != [], "parameters": []}


def swanify_type(solution_slice):
    return [solution_slice[1]]


def swanify_solution_json(solution_slice):
    """내가 만든 solution json 파일을 SWAN이 알아들을 수 있는 json 형식으로 바꾼다."""
    name = swanify_name(solution_slice)
    return_ = swanify_return(solution_slice)
    parameters = swanify_parameters(solution_slice)
    dataIn = swanify_dataIn(solution_slice)
    dataOut = swanify_dataOut(solution_slice)
    securityLevel = "low"
    discovery = "manual"
    framework = "sagan"
    link = ""
    cwe = []
    type_ = swanify_type(solution_slice)
    comment = ""
    return {"name": name, "return": return_,
            "parameters": parameters, "dataIn": dataIn,
            "dataOut": dataOut, "securityLevel": securityLevel,
            "discovery": discovery, "framework": framework,
            "link": link, "cwe": cwe,
            "type": type_, "comment": comment}


def sample_size_by_quantity_and_diversity(quantity, diversity):
    if   quantity == 52  and diversity == 'more_src':
        return MORE_SRC_52
    elif quantity == 100 and diversity == 'more_src':
        return MORE_SRC_100
    elif quantity == 152 and diversity == 'more_src':
        return MORE_SRC_152
    elif quantity == 200 and diversity == 'more_src':
        return MORE_SRC_200

    elif quantity == 52  and diversity == 'more_sin':
        return MORE_SIN_52
    elif quantity == 100 and diversity == 'more_sin':
        return MORE_SIN_100
    elif quantity == 152 and diversity == 'more_sin':
        return MORE_SIN_152
    elif quantity == 200 and diversity == 'more_sin':
        return MORE_SIN_200

    elif quantity == 52  and diversity == 'more_san':
        return MORE_SAN_52
    elif quantity == 100 and diversity == 'more_san':
        return MORE_SAN_100
    elif quantity == 152 and diversity == 'more_san':
        return MORE_SAN_152
    elif quantity == 200 and diversity == 'more_san':
        return MORE_SAN_200

    elif quantity == 52  and diversity == 'more_non':
        return MORE_NON_52
    elif quantity == 100 and diversity == 'more_non':
        return MORE_NON_100
    elif quantity == 152 and diversity == 'more_non':
        return MORE_NON_152
    elif quantity == 200 and diversity == 'more_non':
        return MORE_NON_200

    elif quantity == 52  and diversity == 'fair':
        return FAIR_52
    elif quantity == 100 and diversity == 'fair':
        return FAIR_100
    elif quantity == 152 and diversity == 'fair':
        return FAIR_152
    elif quantity == 200 and diversity == 'fair':
        return FAIR_200


def select_by_sample_sizes(sample_sizes, solution):
    # categorize by labels
    srcs, sins, sans, nons = [], [], [], []
    for item in solution.items():
        if   item[1] == 'src':
            srcs.append(item)
        elif item[1] == 'sin':
            sins.append(item)
        elif item[1] == 'san':
            sans.append(item)
        elif item[1] == 'non':
            nons.append(item)
    src_size, sin_size, san_size, non_size = tuple(sample_sizes)
    sampled_srcs = random.sample(srcs, src_size)
    sampled_sins = random.sample(sins, sin_size)
    sampled_sans = random.sample(sans, san_size)
    sampled_nons = random.sample(nons, non_size)

    return sampled_srcs, sampled_sins, sampled_sans, sampled_nons

# Main =================================================
# ======================================================

def main():
    with open("../BayesianNetwork/solution_sagan.json", "r+") as sagan_solution:
        sagan_json = json.load(sagan_solution)

    sample_sizes = sample_size_by_quantity_and_diversity(QUANTITY, DIVERSITY)

    sampled_srcs, sampled_sins,\
        sampled_sans, sampled_nons = select_by_sample_sizes(sample_sizes, sagan_json)

    samples = sampled_srcs + sampled_sins + sampled_sans + sampled_nons

    swanified_solution_methods = list(map(swanify_solution_json, samples))
    cwes = []
    swanified_solution_json = {
        "methods": swanified_solution_methods,
        "cwes": cwes
    }
    with open("swanified_solution_sagan_"+str(QUANTITY)+"_"+DIVERSITY+".json", "w+") as out:
        json.dump(swanified_solution_json, out, indent=2)

if __name__ == "__main__":
    main()
