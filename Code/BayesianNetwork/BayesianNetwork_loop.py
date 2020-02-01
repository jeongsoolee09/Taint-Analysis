from pomegranate import *
import matplotlib.pyplot as plt
import seaborn; seaborn.set_style('whitegrid')
import time
import random
import numpy as np
import pandas as pd
import csv

start = time.time()

# methods : raw_data.csv
# edges : edges.csv

# 왜 하는지는 모르겠다만
numpy.random.seed(0)
numpy.set_printoptions(suppress=True)

# csv reader 시리즈가 있어서 당장은 필요 없음
# methods = pd.read_csv("raw_data.csv", index_col=0)
# edges = pd.read_csv("edges.csv", index_col=0)

raw_data = open("raw_data.csv", "r+")
dataReader = csv.reader(raw_data)
edges_data = open("edges.csv", "r+")
edgesReader = csv.reader(edges_data)

# 메소드 이름 겹치는 것 (e.g. 메소드 오버라이딩)은 당장은 상관 안할 것.
def submit_distribution_to_pom():
    next(dataReader) # 헤더 맛없어 퉤
    for data in dataReader:
        # code = compile(data[4] + " = DiscreteDistribution({\'src\':0.25, \'sin\':0.25, \'san\':0.25, \'non\':0.25})", "<string>", "exec")
        code = data[4] + " = DiscreteDistribution({\'src\':0.25, \'sin\':0.25, \'san\':0.25, \'non\':0.25})"
        exec(code, globals())

submit_distribution_to_pom()

print("elapsed time :", time.time() - start)
