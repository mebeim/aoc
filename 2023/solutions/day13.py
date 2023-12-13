#!/usr/bin/env python3

import sys

def transpose(grid):
	return list(map(''.join, zip(*grid)))

def count_differences(a, b):
	diff = 0
	for linea, lineb in zip(a, b):
		diff += sum(chara != charb for chara, charb in zip(linea, lineb))
		if diff > 1:
			break

	return diff

def find_reflections(grid):
	height = len(grid)
	perfect = imperfect = 0

	for size in range(1, height // 2 + 1):
		a = grid[:size]
		b = grid[size:2 * size][::-1]
		diff = count_differences(a, b)

		if diff == 0:
			perfect = size
		elif diff == 1:
			imperfect = size

		if perfect and imperfect:
			break

		a = grid[height - 2 * size:height - size]
		b = grid[height - size:][::-1]
		diff = count_differences(a, b)

		if diff == 0:
			perfect = height - size
		elif diff == 1:
			imperfect = height - size

		if perfect and imperfect:
			break

	return perfect, imperfect


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

with fin:
	grids = fin.read().split('\n\n')

ans1 = ans2 = 0

for raw_grid in grids:
	g = raw_grid.splitlines()

	perfect, imperfect = find_reflections(g)
	ans1 += 100 * perfect
	ans2 += 100 * imperfect

	perfect, imperfect = find_reflections(transpose(g))
	ans1 += perfect
	ans2 += imperfect

print('Part 1:', ans1)
print('Part 2:', ans2)
