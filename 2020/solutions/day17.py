#!/usr/bin/env python3

from utils import advent
from itertools import product
from operator import itemgetter

def alive_neighbors(cube, coords):
	ranges = ((c - 1, c, c + 1) for c in coords)
	alive  = sum(p in cube for p in product(*ranges))
	alive -= coords in cube
	return alive

def bounds(cube, n_dims):
	for i in range(n_dims):
		lo = min(map(itemgetter(i), cube)) - 1
		hi = max(map(itemgetter(i), cube)) + 2
		yield range(lo, hi)

def evolve(cube, n_dims):
	new = set()

	for coord in product(*bounds(cube, n_dims)):
		alive = alive_neighbors(cube, coord)
		if (coord in cube and alive in (2, 3)) or alive == 3:
			new.add(coord)

	return new


advent.setup(2020, 17)
fin = advent.get_input()

grid = tuple(map(str.rstrip, fin))
h, w = len(grid), len(grid[0])
cube = set((x, y, 0) for x, y in product(range(h), range(w)) if grid[x][y] == '#')

for _ in range(6):
	cube = evolve(cube, 3)

total_alive = len(cube)
advent.print_answer(1, total_alive)


cube = set((x, y, 0, 0) for x, y in product(range(h), range(w)) if grid[x][y] == '#')

for _ in range(6):
	cube = evolve(cube, 4)

total_alive = len(cube)
advent.print_answer(2, total_alive)
