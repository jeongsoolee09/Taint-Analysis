import networkx as nx


def partition(coll, n):
    # input sanity check
    if n > len(coll):
        raise ValueError("The size of a partition is too large!")
    if n < 0:
        raise ValueError("The size of a partition cannot be negative!")

    # trivial case
    if len(coll) == 0:
        return coll

    # nontrivial case
    acc = []
    i = 0; j = n
    for _ in range(len(coll)//n):
        acc.append(coll[i:j])
        i += n; j += n

    # append leftovers
    if len(coll[i:]) != 0:
        acc.append(coll[i:])

    return acc
