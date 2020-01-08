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

def loop(times):
    for time in range(times):
        i = random.randint(0, max_index_plus_one-1)
        query = methods.loc[i][2]
        if time == 0:  # for debugging purposes.
            x = input("What label does <" + query + "> bear? [src/sin/san/non]: ")
        
        

def bayesian_update(prior):
    pass # not yet implemented
        

loop(20)
