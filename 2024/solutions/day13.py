#!/usr/bin/env python3

import sys
from re import findall

def solve(ax, ay, bx, by, px, py):
	# Solve the linear system of two equations (with a and b unknown):
	#     ax * a + bx * b = px
	#     ay * a + by * b = py

	denominator = ax * by - bx * ay
	if denominator == 0:
		return 0

	a, arem = divmod(px * by - bx * py, denominator)
	if arem != 0:
		return 0

	b, brem = divmod(ax * py - px * ay, denominator)
	if brem != 0:
		return 0

	return a * 3 + b


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

numbers = list(map(int, findall(r'\d+', fin.read())))
total1 = total2 = 0

for i in range(0, len(numbers), 6):
	ax, ay, bx, by, px, py = numbers[i: i + 6]
	total1 += solve(ax, ay, bx, by, px, py)
	total2 += solve(ax, ay, bx, by, px + 10000000000000, py + 10000000000000)

print('Part 1:', total1)
print('Part 2:', total2)

