#!/usr/bin/env python3

from utils import advent
from copy import deepcopy
from itertools import product

def neighbors4(grid, r, c):
	for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
		nr, nc = r + dr, c + dc

		if 0 <= nr < ROWS and 0 <= nc < COLS:
			yield nr, nc

def neighbors4_alive(grid, r, c):
	return sum(grid[nr][nc] for nr, nc in neighbors4(grid, r, c))

def evolve(grid, r, c):
	alive = neighbors4_alive(grid, r, c)

	if grid[r][c] == BUG:
		if alive == 1:
			return BUG
		return EMPTY

	if alive == 1 or alive == 2:
		return BUG
	return EMPTY

def nextgen(grid):
	new_grid = [[EMPTY] * COLS for _ in range(ROWS)]

	for r, c in product(range(ROWS), range(COLS)):
		new_grid[r][c] = evolve(grid, r, c)

	return new_grid

def recursive_evolve(grid, grid_outer, grid_inner, r, c):
	alive = 0

	if grid_outer is not None:
		if c == 0 and grid_outer[CENTER_ROW][CENTER_COL - 1]: # left
			alive += 1
		if r == 0 and grid_outer[CENTER_ROW - 1][CENTER_COL]: # up
			alive += 1
		if c == MAXCOL and grid_outer[CENTER_ROW][CENTER_COL + 1]: # right
			alive += 1
		if r == MAXROW and grid_outer[CENTER_ROW + 1][CENTER_COL]: # down
			alive += 1

	if grid_inner is not None:
		if (r, c) == (CENTER_ROW, CENTER_COL - 1): # left
			alive += sum(grid_inner[i][0] for i in range(ROWS))
		elif (r, c) == (CENTER_ROW - 1, CENTER_COL): # up
			alive += sum(grid_inner[0][i] for i in range(COLS))
		elif (r, c) == (CENTER_ROW, CENTER_COL + 1): # right
			alive += sum(grid_inner[i][MAXCOL] for i in range(ROWS))
		elif (r, c) == (CENTER_ROW + 1, CENTER_COL): # down
			alive += sum(grid_inner[MAXROW][i] for i in range(COLS))

	alive += neighbors4_alive(grid, r, c)

	if grid[r][c] == BUG:
		if alive == 1:
			return BUG
		return EMPTY

	if alive == 1 or alive == 2:
		return BUG
	return EMPTY

def recursive_nextgen(grids, depth):
	if depth in grids:
		grid = grids[depth]
	else:
		grid = [[EMPTY] * COLS for _ in range(ROWS)]

	new_grid = [[EMPTY] * COLS for _ in range(ROWS)]
	grid_outer = grids.get(depth + 1)
	grid_inner = grids.get(depth - 1)

	for r, c in product(range(ROWS), range(COLS)):
		if (r, c) == (CENTER_ROW, CENTER_COL):
			continue

		new_grid[r][c] = recursive_evolve(grid, grid_outer, grid_inner, r, c)

	return new_grid


advent.setup(2019, 24)
fin = advent.get_input()
orig_grid = list(list(l.strip()) for l in fin)

ROWS = len(orig_grid)
COLS = len(orig_grid[0])
MAXROW = ROWS - 1
MAXCOL = COLS - 1
EMPTY, BUG = 0, 1

for r, c in product(range(ROWS), range(COLS)):
	orig_grid[r][c] = BUG if orig_grid[r][c] == '#' else EMPTY

grid = deepcopy(orig_grid)
seen = set()

while True:
	state = tuple(map(tuple, grid))
	if state in seen:
		break

	seen.add(state)
	grid = nextgen(grid)

total, biodiv = 0, 1
for r, c in product(range(ROWS), range(COLS)):
	if grid[r][c] == BUG:
		total += biodiv
	biodiv <<= 1

advent.print_answer(1, total)


assert ROWS % 2 == 1 and COLS % 2 == 1
CENTER_ROW, CENTER_COL = ROWS // 2 + 1, COLS // 2 + 1

grid = deepcopy(orig_grid)
grid[CENTER_ROW][CENTER_COL] = EMPTY
grids = {0: grid}
min_depth = 0
max_depth = 0

for _ in range(200):
	new_grids = {}

	for depth in grids:
		new_grids[depth] = recursive_nextgen(grids, depth)

	min_depth -= 1
	new_grids[min_depth] = recursive_nextgen(grids, min_depth)

	max_depth += 1
	new_grids[max_depth] = recursive_nextgen(grids, max_depth)

	grids = new_grids

bugs = sum(sum(sum(c == BUG for c in row) for row in grid) for grid in grids.values())
advent.print_answer(2, bugs)
