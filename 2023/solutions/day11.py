#!/usr/bin/env python3

import sys

def sum_distances(counts, multiplier):
	total = partial_sum = previous = space = 0

	for n in counts:
		if n:
			total       += (n * (2 * previous + n - 1) // 2) * space
			total       -= n * partial_sum + ((n - 1) * n // 2) * space
			partial_sum += n * space
			previous    += n
			space       += 1
		else:
			space += multiplier

	return total

def solve(row_counts, col_counts, multiplier):
	return sum_distances(row_counts, multiplier) + sum_distances(col_counts, multiplier)


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
