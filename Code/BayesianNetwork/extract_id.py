import pandas as pd

raw_data = pd.read_csv("raw_data.csv")
print()
for row in raw_data.itertuples():
    print('\"'+row.id+'\"')
