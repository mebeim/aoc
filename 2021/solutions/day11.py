#!/usr/bin/env python3

from utils import advent
from itertools import count, product

def neighbors8(r, c, h, w):
	deltas = (
		(1, 0), (-1,  0), ( 0, 1), ( 0, -1),
		(1, 1), ( 1, -1), (-1, 1), (-1, -1)
	)

	for dr, dc in deltas:
		rr, cc = (r + dr, c + dc)
		if 0 <= rr < h and 0 <= cc < w:
			yield rr, cc

def flash(grid, r, c, h, w):
	if grid[r][c] <= 9:
		return

	grid[r][c] = -1

	for nr, nc in neighbors8(r, c, h, w):
		if grid[nr][nc] != -1:
			grid[nr][nc] += 1
			flash(grid, nr, nc, h, w)

def evolve(grid, h, w):
	flashes = 0

	for r, c in product(range(h), range(w)):
		grid[r][c] += 1

	for r, c in product(range(h), range(w)):
		flash(grid, r, c, h, w)

	for r, c in product(range(h), range(w)):
		if grid[r][c] == -1:
			grid[r][c] = 0
			flashes += 1

	return flashes


advent.setup(2021, 11)
fin = advent.get_input()

lines   = map(str.rstrip, fin)
grid    = list(list(map(int, row)) for row in lines)
h, w    = len(grid), len(grid[0])
n_cells = h * w

tot_flashes = sum(evolve(grid, h, w) for _ in range(100))

for sync_step in count(101):
	if evolve(grid, h, w) == n_cells:
		break

advent.print_answer(1, tot_flashes)
advent.print_answer(2, sync_step)
