#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 2)
fin = advent.get_input()
lines = read_lines(fin)


def safe(ints):
	diffs = []

	for a, b in zip(ints, ints[1:]):
		diffs.append(b - a)

	if all(d > 0 for d in diffs) and all(1 <= abs(d) <= 3 for d in diffs):
		return True

	elif all(d < 0 for d in diffs) and all(1 <= abs(d) <= 3 for d in diffs):
		return True

ans1 = ans2 = 0

for line in lines:
	ints = list(map(int, line.split()))

	if safe(ints):
		ans1 += 1
		ans2 += 1
		continue

	for i in range(len(ints)):
		x = ints[:i] + ints[i+1:]

		if safe(x):
			ans2 += 1
			break

advent.print_answer(1, ans1)
advent.print_answer(2, ans2)
