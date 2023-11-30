#!/usr/bin/env python3

import sys
from itertools import product

def neighbors(coords):
	ranges = ((c - 1, c, c + 1) for c in coords)
	yield from product(*ranges)

def all_neighbors(cube):
	return set(n for p in cube for n in neighbors(p))

def alive_neighbors(cube, coords):
	return sum(p in cube for p in neighbors(coords)) - (coords in cube)

def evolve(cube):
	new = set()

	for p in all_neighbors(cube):
		alive = alive_neighbors(cube, p)

		if alive == 3 or (alive == 2 and p in cube):
			new.add(p)

	return new


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

grid = tuple(map(str.rstrip, fin))
h, w = len(grid), len(grid[0])
cube = set((x, y, 0) for x, y in product(range(h), range(w)) if grid[x][y] == '#')

for _ in range(6):
	cube = evolve(cube)

total_alive = len(cube)
print('Part 1:', total_alive)


hypercube = set((x, y, 0, 0) for x, y in product(range(h), range(w)) if grid[x][y] == '#')

for _ in range(6):
	hypercube = evolve(hypercube)

total_alive = len(hypercube)
print('Part 2:', total_alive)
