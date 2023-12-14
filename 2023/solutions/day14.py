#!/usr/bin/env python3

import sys
from operator import itemgetter

def rotate_90(coords, height):
	return set((c, height - r - 1) for r, c in coords)

def move(fixed, movable):
	new_movable = fixed.copy()

	for r, c in sorted(movable, key=itemgetter(0)):
		r -= 1
		while r >= 0 and (r, c) not in new_movable:
			r -= 1

		new_movable.add((r + 1, c))

	return new_movable - fixed

def spin(fixed, movable, height, width, iterations):
	seen = {frozenset(movable): 0}

	cache = [(fixed, height)]
	for _ in range(3):
		cache.append((rotate_90(cache[-1][0], height), width))
		height, width = width, height

	for i in range(1, iterations + 1):
		for fixed, height in cache:
			movable = rotate_90(move(fixed, movable), height)

		key = frozenset(movable)
		if key in seen:
			break

		seen[key] = i
		seen[i]   = key

	cycle_start = seen[key]
	cycle_len   = i - cycle_start
	remaining   = iterations - cycle_start
	final       = remaining % cycle_len + cycle_start

	return sum(map(lambda rc: height - rc[0], seen[final]))


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

grid = fin.read().splitlines()
height, width = len(grid), len(grid[0])
fixed = set()
movable = set()

for r, row in enumerate(grid):
	for c, char in enumerate(row):
		if char == '#':
			fixed.add((r, c))
		elif char == 'O':
			movable.add((r, c))

total1 = sum(map(lambda rc: height - rc[0], move(fixed, movable)))
print('Part 1:', total1)

total2 = spin(fixed, movable, height, width, 1000000000)
print('Part 2:', total2)
