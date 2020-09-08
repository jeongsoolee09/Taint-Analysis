import pandas as pd
test = pd.DataFrame({('A', 'a'):[1,2,3,4,5], ('A', 'b'):[5,4,3,2,1], ('B', 'a'):[5,2,3,4,1], ('B','b'):[1,4,3,2,5]})

print()
test['idx'] = test.index * 2  # adding auxiliary column 'idx' (all even)

test2 = test.iloc[:, [2,3,0,1,4]]   # creating flipped DF
test2.columns = test.columns  # fixing column names
test2['idx'] = test2.index * 2 + 1  # for flipped DF column 'idx' is all odd

df = pd.concat([test, test2])
df = df.sort_values(by='idx')
print(df)
df = df.set_index('idx')
print(df)

df = df.drop_duplicates()  # remove rows with duplicates 
print(df)
df = df[df.index%2 == 0]  # remove rows with odd idx (flipped)
df = df.reset_index()[['A', 'B']] 
print(df)
