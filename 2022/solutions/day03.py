#!/usr/bin/env python3

import sys

def prio(x):
    return ord(x) - (96 if x >= 'a' else 38)


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

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

print('Part 1:', total)
print('Part 2:', group_total)
