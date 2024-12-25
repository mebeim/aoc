#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 25)
fin = advent.get_input()

data = fin.read()
ans1 = 0
schems = data.split('\n\n')
keys = []
locks = []

for schem in schems:
	grid = schem.splitlines()
	if grid[0] == '#####':
		locks.append(grid)
	else:
		keys.append(grid)

def fit(l, k):
	for lrow, krow in zip(l, k):
		for lc, kc in zip(lrow, krow):
			if lc == '#' and kc == '#':
				return False

	return True

for l in locks:
	for k in keys:
		ans1 += fit(l, k)

advent.print_answer(1, ans1)
