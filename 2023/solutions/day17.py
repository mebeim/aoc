#!/usr/bin/env python3

import sys
import heapq
from math import inf as INFINITY
from itertools import chain
from collections import defaultdict
from functools import partial

def straight_line(grid, height, width, r, c, dr, dc, start, stop):
	weight = 0

	for i in range(1, stop + 1):
		r += dr
		c += dc

		if not (0 <= r < height and 0 <= c < width):
			break

		weight += grid[r][c]

		if i >= start:
			yield (r, c), weight

def neighbors(node, start, stop):
	coords, vertical = node
	gen = straight_line(*coords, +vertical, +(not vertical), start, stop)
	gen = chain(gen, straight_line(*coords, -vertical, -(not vertical), start, stop))

	for coords, weight in gen:
		yield (coords, not vertical), weight

def dijkstra(src_coords, dst_coords, straight_start, straight_stop):
	distance = defaultdict(lambda: INFINITY)
	queue    = [(0, (src_coords, False)), (0, (src_coords, True))]
	visited  = set()

	while queue:
		dist, node = heapq.heappop(queue)
		if node[0] == dst_coords:
			return dist

		if node in visited:
			continue

		visited.add(node)

		for neighbor, weight in neighbors(node, straight_start, straight_stop):
			new_dist = dist + weight

			if new_dist < distance[neighbor]:
				distance[neighbor] = new_dist
				heapq.heappush(queue, (new_dist, neighbor))

	return INFINITY


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1], 'r') if len(sys.argv) > 1 else sys.stdin

with fin:
	grid = fin.read().splitlines()

grid = [list(map(int, row)) for row in grid]
height, width = len(grid), len(grid[0])

# Cheating to avoid manually passing these 3 arguments to every single function
straight_line = partial(straight_line, grid, height, width)

src = (0, 0)
dst = (height - 1, width - 1)

min_dist = dijkstra(src, dst, 1, 3)
print('Part 1:', min_dist)

min_dist = dijkstra(src, dst, 4, 10)
print('Part 2:', min_dist)
