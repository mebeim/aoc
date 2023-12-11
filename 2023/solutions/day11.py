#!/usr/bin/env python3

import sys

def adjust(row, multiplier):
	res = []
	space = 0

	for n in row:
		for _ in range(n):
			yield space

		space += 1 if n else multiplier

	return res

def sum_distances(values):
	total = partial_sum = 0

	for i, v in enumerate(values):
		total += i * v - partial_sum
		partial_sum += v

	return total

def solve(row_counts, col_counts, multiplier):
	return sum_distances(adjust(row_counts, multiplier)) + \
		sum_distances(adjust(col_counts, multiplier))


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

grid = list(map(str.rstrip, fin))
row_counts = [0] * len(grid)
col_counts = [0] * len(grid[0])

for r, row in enumerate(grid):
	for c, cell in enumerate(row):
		if cell == '#':
			row_counts[r] += 1
			col_counts[c] += 1

total1 = solve(row_counts, col_counts, 2)
print('Part 1:', total1)

total2 = solve(row_counts, col_counts, 1000000)
print('Part 2:', total2)
