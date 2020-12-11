#!/usr/bin/env python3

from utils import advent
from copy import deepcopy

def occupied_neighbors(grid, r, c):
	deltas = (
		(-1, 0), ( 1,  0), (0, 1), ( 0, -1),
		(-1, 1), (-1, -1), (1, 1), ( 1, -1)
	)

	total = 0
	for dr, dc in deltas:
		rr, cc = r + dr, c + dc
		if 0 <= rr <= MAXROW and 0 <= cc <= MAXCOL:
			total += grid[rr][cc] == OCCUPIED

	return total

def occupied_in_sight(grid, r, c):
	deltas = (
		(-1, 0), ( 1,  0), (0, 1), ( 0, -1),
		(-1, 1), (-1, -1), (1, 1), ( 1, -1)
	)

	total = 0
	for dr, dc in deltas:
		rr, cc = r + dr, c + dc

		while 0 <= rr <= MAXROW and 0 <= cc <= MAXCOL:
			if grid[rr][cc] != FLOOR:
				if grid[rr][cc] == OCCUPIED:
					total += 1
				break

			rr += dr
			cc += dc

	return total


advent.setup(2020, 11)
fin = advent.get_input()

original = list(map(list, map(str.rstrip, fin.readlines())))
MAXROW, MAXCOL = len(original) - 1, len(original[0]) - 1
OCCUPIED, EMPTY, FLOOR = '#L.'

grid = deepcopy(original)

while 1:
	previous = deepcopy(grid)

	for r, row in enumerate(previous):
		for c, cell in enumerate(row):
			if cell == FLOOR:
				continue

			occ = occupied_neighbors(previous, r, c)

			if cell == EMPTY and occ == 0:
				grid[r][c] = OCCUPIED
			elif cell == OCCUPIED and occ >= 4:
				grid[r][c] = EMPTY

	if grid == previous:
		break

total_occupied = sum(row.count(OCCUPIED) for row in grid)
advent.print_answer(1, total_occupied)


grid = deepcopy(original)

while 1:
	previous = deepcopy(grid)

	for r, row in enumerate(previous):
		for c, cell in enumerate(row):
			if cell == FLOOR:
				continue

			occ = occupied_in_sight(previous, r, c)

			if cell == EMPTY and occ == 0:
				grid[r][c] = OCCUPIED
			elif cell == OCCUPIED and occ >= 5:
				grid[r][c] = EMPTY

	if grid == previous:
		break

	previous = grid

total_occupied = sum(row.count(OCCUPIED) for row in grid)
advent.print_answer(2, total_occupied)
