#!/usr/bin/env python3

from utils import advent

import sys
import heapq
from string import *
from collections import defaultdict, deque, namedtuple, Counter

advent.setup(2018, 14)
fin = advent.get_input()
# print(*fin)

##################################################

target = int(fin.read().strip())
targetscores = tuple(map(int, str(target)))
targetlen = len(targetscores)

recipes = [3, 7]
tot = 2
turn = 0
elf1 = 0
elf2 = 1

lastchecked = 0

# print(elf1, elf2, recipes)

done = False

while True:
	s = str(recipes[elf1] + recipes[elf2])
	tot += len(s)

	for newr in map(int, s):
		recipes.append(newr)

	# print(elf1, elf2, recipes)

	# if tot >= target + 10:
	# 	break

	if lastchecked <= tot - targetlen:
		while lastchecked <= tot - targetlen:
			done = False
			ok = 0

			for i, r in enumerate(recipes[lastchecked:]):
				# print('  ', lastchecked, i, r, targetscores[i])

				if targetscores[i] == r:
					ok += 1
				else:
					break

				if ok == targetlen:
					ans2 = lastchecked
					done = True
					break

			if done:
				break

			lastchecked += 1

	if done:
		break

	elf1 = (elf1 + recipes[elf1] + 1) % len(recipes)
	elf2 = (elf2 + recipes[elf2] + 1) % len(recipes)

	turn += 1
	turn %= 2

ans = ''.join(map(str, recipes[target:target+10]))

advent.submit_answer(1, ans)
advent.submit_answer(2, ans2)
