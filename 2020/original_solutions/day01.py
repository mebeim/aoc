#!/usr/bin/env python3

from utils.all import *

fin = advent.get_input()
eprint(*fin, sep=''); fin.seek(0, 0)

ints = get_ints(fin, True)

print(ints)
for i, x in enumerate(ints):
	for j, y in enumerate(ints):
		if i != j:
			if x + y == 2020:
				ans = x * y

advent.submit_answer(1, ans)

for i, x in enumerate(ints):
    for j, y in enumerate(ints):
        for k, z in enumerate(ints):
            if len(set([i, j, k])) == 3:
                if x + y + z == 2020:
                    ans = x * y * z

advent.submit_answer(2, ans)
