#!/usr/bin/env python3

from utils import advent
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


advent.setup(2020, 17)
fin = advent.get_input()

grid = tuple(map(str.rstrip, fin))
h, w = len(grid), len(grid[0])
cube = set((x, y, 0) for x, y in product(range(h), range(w)) if grid[x][y] == '#')

for _ in range(6):
	cube = evolve(cube)

total_alive = len(cube)
advent.print_answer(1, total_alive)


hypercube = set((x, y, 0, 0) for x, y in product(range(h), range(w)) if grid[x][y] == '#')

for _ in range(6):
	hypercube = evolve(hypercube)

total_alive = len(hypercube)
advent.print_answer(2, total_alive)
