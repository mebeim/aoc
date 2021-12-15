#!/usr/bin/env python3

from utils import advent
import heapq
from math import inf as INFINITY
from collections import defaultdict
from itertools import filterfalse

def neighbors4(r, c, h, w):
	for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
		rr, cc = (r + dr, c + dc)
		if 0 <= rr < w and 0 <= cc < h:
			yield rr, cc

def dijkstra(grid):
	h, w = len(grid), len(grid[0])
	source = (0, 0)
	destination = (h - 1, w - 1)

	queue = [(0, source)]
	mindist = defaultdict(lambda: INFINITY, {source: 0})
	visited = set()

	while queue:
		dist, node = heapq.heappop(queue)

		if node == destination:
			return dist

		if node in visited:
			continue

		visited.add(node)
		r, c = node

		for neighbor in filterfalse(visited.__contains__, neighbors4(r, c, h, w)):
			nr, nc  = neighbor
			newdist = dist + grid[nr][nc]

			if newdist < mindist[neighbor]:
				mindist[neighbor] = newdist
				heapq.heappush(queue, (newdist, neighbor))

	return INFINITY


advent.setup(2021, 15)
fin = advent.get_input()

grid    = list(list(map(int, row)) for row in map(str.rstrip, fin))
minrisk = dijkstra(grid)

advent.print_answer(1, minrisk)


tilew = len(grid)
tileh = len(grid[0])

for _ in range(4):
	for row in grid:
		tail = row[-tilew:]
		row.extend((x + 1) if x < 9 else 1 for x in tail)

for _ in range(4):
	for row in grid[-tileh:]:
		row = [(x + 1) if x < 9 else 1 for x in row]
		grid.append(row)

minrisk = dijkstra(grid)
advent.print_answer(2, minrisk)
