#!/usr/bin/env python3

import sys
from math import prod
from collections import defaultdict

def adjacent_symbols(grid, r, start_c, height, width):
	row   = grid[r]
	above = grid[r - 1] if r > 0 else []
	below = grid[r + 1] if r < height - 1 else []

	for c in range(max(0, start_c - 1), width):
		if above and above[c] not in '0123456789.':
			yield (r - 1, c)

		if below and below[c] not in '0123456789.':
			yield (r + 1, c)

		if row[c] not in '0123456789':
			if row[c] != '.':
				yield (r, c)

			if c > start_c:
				break

def extract_number(row, start, length):
	end = start + 1
	while end < length and row[end].isdigit():
		end += 1

	return int(row[start:end])


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

grid = list(map(str.rstrip, fin.readlines()))
height, width = len(grid), len(grid[0])
adj_numbers = defaultdict(list)
answer1 = answer2 = 0

for r, row in enumerate(grid):
	c = 0

	while c < width:
		while c < width and not row[c].isdigit():
			c += 1

		if c >= width:
			break

		symbols = list(adjacent_symbols(grid, r, c, height, width))

		if symbols:
			number = extract_number(row, c, width)
			answer1 += number

			for sym in symbols:
				adj_numbers[sym].append(number)

		while c < width and row[c].isdigit():
			c += 1

print('Part 1:', answer1)

answer2 = sum(map(prod, filter(lambda x: len(x) == 2, adj_numbers.values())))
print('Part 2:', answer2)
