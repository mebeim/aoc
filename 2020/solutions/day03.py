#!/usr/bin/env python3

from utils import advent
from itertools import count

advent.setup(2020, 3)
fin = advent.get_input()

grid = [l.rstrip() for l in fin]
height, width = len(grid), len(grid[0])
trees = 0

for row, col in zip(range(height), count(0, 3)):
	if grid[row][col % width] == '#':
		trees += 1

advent.print_answer(1, trees)


total = trees

for dr, dc in ((1, 1), (1, 5), (1, 7), (2, 1)):
	trees = 0

	for row, col in zip(range(0, height, dr), count(0, dc)):
		if grid[row][col % width] == '#':
			trees += 1

	total *= trees

advent.print_answer(2, total)
