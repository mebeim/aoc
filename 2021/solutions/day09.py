#!/usr/bin/env python3

from utils import advent
from collections import deque

def neighbors4(r, c, h, w):
	for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
		rr, cc = (r + dr, c + dc)
		if 0 <= rr < h and 0 <= cc < w:
			yield (rr, cc)

def bfs(grid, r, c, h, w):
	queue   = deque([(r, c)])
	visited = set()

	while queue:
		rc = queue.popleft()
		if rc in visited:
			continue

		visited.add(rc)

		for nr, nc in neighbors4(*rc, h, w):
			if grid[nr][nc] != 9 and (nr, nc) not in visited:
				queue.append((nr, nc))

	return visited

def connected_components_sizes(grid, h, w):
	visited = set()

	for r in range(h):
		for c in range(w):
			if grid[r][c] != 9 and (r, c) not in visited:
				component = bfs(grid, r, c, h, w)
				visited |= component
				yield len(component)


advent.setup(2021, 9)
fin = advent.get_input()

lines = map(str.rstrip, fin)
grid  = tuple(tuple(map(int, row)) for row in lines)
h, w  = len(grid), len(grid[0])
total = 0

for r, row in enumerate(grid):
	for c, cell in enumerate(row):
		if all(grid[nr][nc] > cell for nr, nc in neighbors4(r, c, h, w)):
			total += cell + 1

advent.print_answer(1, total)


sizes  = sorted(connected_components_sizes(grid, h, w), reverse=True)
answer = sizes[0] * sizes[1] * sizes[2]

advent.print_answer(2, answer)
