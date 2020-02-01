from pomegranate import *
import matplotlib.pyplot as plt
import seaborn; seaborn.set_style('whitegrid')
import time
import random
import numpy as np
import csv

# methods : raw_data.csv
# edges : edges.csv

# 그래프에 싸이클이 없는 것을 확인함. ==> Bayesian Network로 변환 가능

numpy.random.seed(0)
numpy.set_printoptions(suppress=True)

with open("raw_data.csv", "r+") as raw_data:
    dataReader = csv.reader(raw_data)

with open("edges.csv", "r+") as edges:
    edgeReader = csv.reader(edges)

