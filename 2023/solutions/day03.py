#!/usr/bin/env python3

import sys
from math import prod
from collections import defaultdict, deque

def neighbors(grid, r, c, h, w):
	for dr, dc in ((-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)):
		rr, cc = r + dr, c + dc
		if 0 <= rr < h and 0 <= cc < w:
			yield rr, cc, grid[rr][cc]

def adjacent_symbols(grid, r, c, h, w):
	queue = deque(neighbors(grid, r, c, h, w))
	visited = set()
	res = []

	while queue:
		r, c, char = queue.popleft()
		if (r, c) in visited:
			continue

		visited.add((r, c))

		if char not in '0123456789':
			if char != '.':
				res.append((r, c))
			continue

		queue.extend(neighbors(grid, r, c, h, w))

	return res

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

for r, row in enumerate(grid):
	c = 0

	while c < width:
		while c < width and not row[c].isdigit():
			c += 1

		if c >= width:
			break

		symbols = adjacent_symbols(grid, r, c, height, width)
		if symbols:
			number = extract_number(row, c, width)

			for sym in symbols:
				adj_numbers[sym].append(number)

		while c < width and row[c].isdigit():
			c += 1

answer1 = sum(map(sum, adj_numbers.values()))
print('Part 1:', answer1)

answer2 = sum(map(prod, filter(lambda x: len(x) == 2, adj_numbers.values())))
print('Part 2:', answer2)
