#!/usr/bin/env python3

from collections import deque
from math import inf as INFINITY
from itertools import filterfalse

from utils import advent

def neighbors4(grid, r, c, h, w):
	for nr, nc in ((r + 1, c), (r - 1, c), (r, c + 1), (r, c - 1)):
		if 0 <= nr < h and 0 <= nc < w:
			yield nr, nc

def neighbors_forward(grid, r, c, h, w):
	max_el = grid[r][c] + 1
	neigh = neighbors4(grid, r, c, h, w)
	yield from ((nr, nc) for nr, nc in neigh if grid[nr][nc] <= max_el)

def neighbors_backward(grid, r, c, h, w):
	min_el = grid[r][c] - 1
	neigh = neighbors4(grid, r, c, h, w)
	yield from ((nr, nc) for nr, nc in neigh if grid[nr][nc] >= min_el)

def bfs(grid, src, dst, get_neighbors):
	h, w    = len(grid), len(grid[0])
	queue   = deque([(0, src)])
	visited = set()

	while queue:
		distance, rc = queue.popleft()
		r, c = rc

		if rc == dst or grid[r][c] == dst:
			return distance

		if rc not in visited:
			visited.add(rc)

			for n in get_neighbors(grid, r, c, h, w):
				if n in visited:
					continue

				queue.append((distance + 1, n))

	return best


advent.setup(2022, 12)

with advent.get_input(mode='rb') as fin:
	grid = list(map(list, fin.read().splitlines()))

START, END, LOWEST, HIGHEST = b'SEaz'
src = dst = None

for r, row in enumerate(grid):
	for c, cell in enumerate(row):
		if cell == START:
			src = r, c
			grid[r][c] = LOWEST
		elif cell == END:
			dst = r, c
			grid[r][c] = HIGHEST

	if src and dst:
		break

min_dist = bfs(grid, src, dst, neighbors_forward)
advent.print_answer(1, min_dist)

min_dist_from_any_a = bfs(grid, dst, LOWEST, neighbors_backward)
advent.print_answer(2, min_dist_from_any_a)
