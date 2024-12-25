#!/usr/bin/env python3

import sys


def grid_to_set(grid):
	points = set()

	for r, row in enumerate(grid):
		for c, char in enumerate(row):
			if char == '#':
				points.add((r, c))

	return points, row == '#####'


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

locks = []
keys = []

for grid in map(str.splitlines, fin.read().split('\n\n')):
	points, is_key = grid_to_set(grid)

	if is_key:
		keys.append(points)
	else:
		locks.append(points)

n_fitting_pairs = sum(l.isdisjoint(k) for l in locks for k in keys)
print('Part 1:', n_fitting_pairs)
