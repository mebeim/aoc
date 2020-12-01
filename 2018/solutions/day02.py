#!/usr/bin/env python3

from utils import advent
from string import ascii_letters
from collections import Counter

advent.setup(2018, 2)
fin = advent.get_input()

ids = list(map(str.rstrip, fin))
counts = list(map(Counter, ids))

two_letters = sum(2 in c.values() for c in counts)
three_letters = sum(3 in c.values() for c in counts)

ans = two_letters * three_letters
advent.print_answer(1, ans)


l = len(ids[0])
assert all(len(x) == l for x in ids)

done = False

for i in range(l):
	seen = set()

	for cur in ids:
		s = cur[:i] + cur[i+1:]

		if s in seen:
			done = True
			break

		seen.add(s)

	if done:
		break

advent.print_answer(2, s)
