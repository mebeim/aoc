#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 13)
DEBUG = 'debug' in map(str.lower, sys.argv)
fin = advent.get_input() if not DEBUG else io.StringIO('''\
#.##..##.
..#.##.#.
##......#
##......#
..#.##.#.
..##..##.
#.#.##.#.

#...##..#
#....#..#
..##..###
#####.##.
#####.##.
..##..###
#....#..#
''')
data = fin.read()


def find_reflection(grid):
	h   = len(grid)
	mid = h // 2

	for size in range(1, mid + 1):
		a = grid[:size]
		b = grid[size:2 * size][::-1]
		if a == b:
			return size

		a = grid[h - 2 * size:h - size]
		b = grid[h - size:][::-1]
		if a == b:
			return h - size

	return 0

def find_reflection2(grid):
	h   = len(grid)
	mid = h // 2

	for size in range(1, mid + 1):
		a = grid[:size]
		b = grid[size:2 * size][::-1]

		diff = 0
		for x, y in zip(a, b):
			diff += sum(xx != yy for xx, yy in zip(x, y))

		if diff == 1:
			return size

		a = grid[h - 2 * size:h - size]
		b = grid[h - size:][::-1]

		diff = 0
		for x, y in zip(a, b):
			diff += sum(xx != yy for xx, yy in zip(x, y))

		if diff == 1:
			return h - size

	return 0


data = data.split('\n\n')
grids = []
ans1 = ans2 = 0

for d in data:
	grids.append(d.splitlines())

for g in grids:
	ans1 += 100 * find_reflection(g)
	ans2 += 100 * find_reflection2(g)

	g = list(map(''.join, map(''.join, zip(*g))))
	ans1 += find_reflection(g)
	ans2 += find_reflection2(g)

advent.print_answer(1, ans1)
advent.print_answer(2, ans2)
