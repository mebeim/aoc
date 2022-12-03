#!/usr/bin/env python3

from utils import advent

def prio(x):
	if 'a' <= x <= 'z':
		return ord(x) - ord('a') + 1
	return ord(x) - ord('A') + 27


advent.setup(2022, 3)
fin = advent.get_input()

groups = []
total1 = total2 = 0

for i, line in enumerate(fin):
	if i % 3 == 0:
		last = []
		groups.append(last)

	mid = len(line) // 2
	a, b = line[:mid], line[mid:]
	last.append(line)

	for item in a:
		if item in b:
			total1 += prio(item)
			break

advent.print_answer(1, total1)


for a, b, c in groups:
	for item in a:
		if item in b and item in c:
			total2 += prio(item)
			break

advent.print_answer(2, total2)
