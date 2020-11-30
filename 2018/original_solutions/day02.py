#!/usr/bin/env python3

from utils import advent

advent.setup(2018, 2)
fin = advent.get_input()

ans = 0
ans2 = 0

##################################################

from string import ascii_letters
from collections import Counter

twos = 0
threes = 0

ids = list(map(str.rstrip, fin))
counts = list(map(Counter, ids))

for cur in counts:
	counts = Counter(cur)
	ok2 = False
	ok3 = False

	for n in cur.values():
		if not ok2 and n == 2:
			twos += 1
			ok2 = True
		elif not ok3 and n == 3:
			threes += 1
			ok3 = True

		if ok2 and ok3:
			break

ans = twos * threes

advent.submit_answer(1, ans)

for a in ids:
	for b in ids:
		diff = 0

		for c1, c2 in zip(a, b):
			if c1 != c2:
				diff += 1

			if diff > 1:
				break

		if diff == 1:
			break

	if diff == 1:
		break

ans2 = ''.join(map(lambda c: '' if c[0] != c[1] else c[0], zip(a, b)))

advent.submit_answer(2, ans2)
