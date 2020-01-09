import pandas as pd
import time
import random
from re import match

methods = pd.read_csv("raw_data.csv", index_col=0)
edges = pd.read_csv("edges.csv", index_col=0)

# 1. 다음을 20번 반복한다:
# 2.     사용자에게 아무 메소드나 뽑아서 물어본다: "저기요, 이거 레이블이 뭐에요?"
# 3.     사용자가 L (어떤 레이블)이라고 대답한다.
# 4.     사용자의 대답을 듣고, 엣지로 연결된 모든 메소드들의 L 확률을 전부 베이즈규칙을 활용해 업데이트한다.

max_index_plus_one = methods.shape[0]

# Prior belief를 나타내는 자료구조 만들기
priors = pd.DataFrame(index=methods.index, columns=["src", "sin", "san", "non"])
priors = priors.fillna(0.25) # Flat priors!


def loop(times):
    for time in range(times):
        i = random.randint(0, max_index_plus_one-1)
        query = methods.loc[i][2]
        if time == 0:  # for debugging purposes.
            oracle_response = input("What label does <" + query + "> bear? [src/sin/san/non]: ")
        if oracle_response == 'src':
            bayesian_update(i, priors.loc[i], 'src')
        elif oracle_response == 'sin':
            bayesian_update(i, priors.loc[i], 'sin')
        elif oracle_response == 'san':
            bayesian_update(i, priors.loc[i], 'san')
        elif oracle_response == 'non':
            bayesian_update(i, priors.loc[i], 'non')
            

def bayesian_update(method_index, prior, oracle_response):
    if oracle_response == 'src':
        prior[0] = 1 * prior[0] / 0.25     # src
        prior[1] = 0 * prior[1] / 0.25     # sin
        prior[2] = 0 * prior[2] / 0.25     # san
        prior[3] = 0 * prior[3] / 0.25     # non
    elif oracle_response == 'sin':
        prior[0] = 0 * prior[0] / 0.25     # src
        prior[1] = 1 * prior[1] / 0.25     # sin
        prior[2] = 0 * prior[2] / 0.25     # san
        prior[3] = 0 * prior[3] / 0.25     # non
    elif oracle_response == 'san':
        prior[0] = 0 * prior[0] / 0.25     # src
        prior[1] = 0 * prior[1] / 0.25     # sin
        prior[2] = 1 * prior[2] / 0.25     # san
        prior[3] = 0 * prior[3] / 0.25     # non
    elif oracle_response == 'non':
        prior[0] = 0 * prior[0] / 0.25     # src
        prior[1] = 0 * prior[1] / 0.25     # sin
        prior[2] = 0 * prior[2] / 0.25     # san
        prior[3] = 1 * prior[3] / 0.25     # non
    belief_propagation(method_index)
        

def belief_propagation(node):
    """do it recursively"""

    # belief_propagation()
    
loop(20)
