#!/usr/bin/env python3

from utils import advent
import re
from itertools import product
from operator import itemgetter

MOVEMAP = {
	'e' : ( 1,  0),
	'w' : (-1,  0),
	'se': ( 1,  1),
	'sw': ( 0,  1),
	'ne': ( 0, -1),
	'nw': (-1, -1)
}

def walk(moves):
	x, y = 0, 0

	for move in moves:
		dx, dy = MOVEMAP[move]
		x += dx
		y += dy

	return x, y

def black_adjacent(grid, x, y):
	deltas = ((1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1))
	return sum((x + dx, y + dy) in grid for dx, dy in deltas)

def bounds(grid):
	lox = min(map(itemgetter(0), grid)) - 1
	loy = min(map(itemgetter(1), grid)) - 1
	hix = max(map(itemgetter(0), grid)) + 2
	hiy = max(map(itemgetter(1), grid)) + 2
	return range(lox, hix), range(loy, hiy)

def evolve(grid):
	new = set()

	for p in product(*bounds(grid)):
		n = black_adjacent(grid, *p)

		if p in grid and not (n == 0 or n > 2):
			new.add(p)
		elif p not in grid and n == 2:
			new.add(p)

	return new


advent.setup(2020, 24)
fin = advent.get_input()

grid = set() # coords of tiles with black side up
rexp = re.compile(r'e|w|se|sw|ne|nw')

for line in fin:
	moves = rexp.findall(line)
	p = walk(moves)

	if p in grid:
		grid.remove(p)
	else:
		grid.add(p)

n_black = len(grid)
advent.print_answer(1, n_black)


for _ in range(100):
	grid = evolve(grid)

n_black = len(grid)
advent.print_answer(2, n_black)
