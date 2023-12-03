#!/usr/bin/env python3

import sys
from math import prod
from collections import defaultdict

def adjacent_symbols(grid, r, start_c, height, width):
	row   = grid[r]
	above = grid[r - 1] if r > 0 else []
	below = grid[r + 1] if r < height - 1 else []
	gears = []
	adj_to_symbol = False

	for c in range(max(0, start_c - 1), width):
		if above and above[c] not in '0123456789.':
			adj_to_symbol = True
			if above[c] == '*':
				gears.append((r - 1, c))

		if below and below[c] not in '0123456789.':
			adj_to_symbol = True
			if below[c] == '*':
				gears.append((r + 1, c))

		if not row[c].isdigit():
			adj_to_symbol |= row[c] != '.'
			if row[c] == '*':
				gears.append((r, c))

			if c > start_c:
				break

	return adj_to_symbol, gears

def extract_number(row, start, length):
	end = start + 1
	while end < length and row[end].isdigit():
		end += 1

	return int(row[start:end])


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

grid = list(map(str.rstrip, fin.readlines()))
height, width = len(grid), len(grid[0])

answer1 = answer2 = 0
gears = defaultdict(list)

for r, row in enumerate(grid):
	c = 0

	while c < width:
		while c < width and not row[c].isdigit():
			c += 1

		if c >= width:
			break

		adj_to_symbol, adj_gears = adjacent_symbols(grid, r, c, height, width)

		if adj_to_symbol:
			number = extract_number(row, c, width)
			answer1 += number

			for rc in adj_gears:
				gears[rc].append(number)

		while c < width and row[c].isdigit():
			c += 1

print('Part 1:', answer1)

answer2 = sum(map(prod, filter(lambda x: len(x) == 2, gears.values())))
print('Part 2:', answer2)
