from solutions import *
import json

with open("solution_sagan.json", "w+") as sagan:
    json.dump(correct_solution_sagan, sagan, indent=2)
with open("solution_WhatIWantExample.json", "w+") as wwe:
    json.dump(correct_solution_WhatIWantExample, wwe, indent=2)
with open("solution_relational.json", "w+") as relational:
    json.dump(correct_solution_relational, relational, indent=2)
