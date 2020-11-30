#!/usr/bin/env python3

from utils import advent
from collections import defaultdict
from string import ascii_lowercase

advent.setup(2018, 5)

fin = advent.get_input()
ans = 0
ans2 = 0

##################################################

units = list(map(ord, fin.read().rstrip()))

def react():
	global units

	change = False

	for i in range(len(units)-1):
		if units[i] == units[i+1] + 32 or units[i] + 32 == units[i+1]:
			units[i] = 0
			units[i+1] = 0
			change = True

	units = list(filter(bool, units))

	return change

while react():
	continue

ans = 0
for c in units:
	if c:
		ans += 1

advent.submit_answer(1, ans)

results = []

fin = advent.get_input()
iunits = list(map(ord, fin.read().rstrip()))

for l in map(ord, ascii_lowercase):
	units = iunits[:]
	print('--',chr(l),'->', end=' ')

	for i in range(len(units)):
		if (units[i] == l - 32 or units[i] == l):
			units[i] = 0

	units = list(filter(bool, units))

	while react():
		continue

	print(len(units))

	results.append(len(units))

ans2 = min(results)

advent.submit_answer(2, ans2)
