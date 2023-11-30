#!/usr/bin/env python3

import sys
from itertools import count

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

grid = [l.rstrip() for l in fin]
height, width = len(grid), len(grid[0])
trees = 0

for row, col in zip(range(height), count(0, 3)):
	if grid[row][col % width] == '#':
		trees += 1

print('Part 1:', trees)


total = trees

for dr, dc in ((1, 1), (1, 5), (1, 7), (2, 1)):
	trees = 0

	for row, col in zip(range(0, height, dr), count(0, dc)):
		if grid[row][col % width] == '#':
			trees += 1

	total *= trees

print('Part 2:', total)
