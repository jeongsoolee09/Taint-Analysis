import modin.pandas as pd
from itertools import product

ALL_POSSIBLE_CASES = pd.DataFrame(list(product([1, 2, 3, 4], [1, 2, 3, 4],
                                               [1, 2, 3, 4], [1, 2, 3, 4])))
FIRST_WEIGHT = 1
SECOND_WEIGHT = 4
THIRD_WEIGHT = 64
FOURTH_WEIGHT = 256

# FIRST_WEIGHT = 1
# SECOND_WEIGHT = 1
# THIRD_WEIGHT = 1
# FOURTH_WEIGHT = 1

def weight_mag(mag):
    """주어진 mag에 weight parameter를 곱한다."""
    acc = []
    for i in mag:
        if i == 1:
            acc.append(i*FIRST_WEIGHT)
        elif i == 2:
            acc.append(i*SECOND_WEIGHT)
        elif i == 3:
            acc.append(i*THIRD_WEIGHT)
        elif i == 4:
            acc.append(i*FOURTH_WEIGHT)
    return acc


def make_weighted_mag_table():
    return ALL_POSSIBLE_CASES.apply(weight_mag, result_type="expand")


def assign_prob_to_weighted_case(weighted_mag):
    denominator = weighted_mag.sum()
    acc = []
    formula = lambda x: x / denominator
    for numerator in weighted_mag:
        acc.append(formula(numerator))
    return acc


def make_CPT_lookup_table(weighted_mag_table):
    prob_assigned = weighted_mag_table.apply(assign_prob_to_weighted_case, result_type="expand", axis=1)
    return pd.concat([ALL_POSSIBLE_CASES, prob_assigned], axis=1)


def main():
    weighted_mag_table = make_weighted_mag_table()
    CPT_lookup_table = make_CPT_lookup_table(weighted_mag_table)
    CPT_lookup_table.to_csv("CPT_lookup_table.csv", mode="w+", header=False, index=False)


if __name__ == "__main__":
    main()
