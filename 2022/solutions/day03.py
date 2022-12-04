#!/usr/bin/env python3

from utils import advent

def prio(x):
    return ord(x) - (96 if x >= 'a' else 38)


advent.setup(2022, 3)
fin = advent.get_input()

group = []
total = group_total = 0

for line in fin:
	mid = len(line) // 2
	a, b = line[:mid], line[mid:]

	for letter in a:
		if letter in b:
			total += prio(letter)
			break

	group.append(line)

	if len(group) == 3:
		a, b, c = group
		group = []

		for item in a:
			if item in b and item in c:
				group_total += prio(item)
				break

advent.print_answer(1, total)
advent.print_answer(2, group_total)
