#!/usr/bin/env python3

from utils import advent
import heapq
from functools import lru_cache
from collections import deque, defaultdict
from math import inf as INFINITY

def neighbors4(grid, r, c):
	for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
		rr, cc = (r + dr, c + dc)
		if 0 <= rr < len(grid) and 0 <= cc < len(grid[rr]):
			if grid[rr][cc] != '#':
				yield (rr, cc)

@lru_cache(2**20)
def distance_for_keys(keys):
	return defaultdict(lambda: INFINITY)

@lru_cache(2**20)
def reachable_keys(src, mykeys):
	distance  = distance_for_keys(mykeys)
	queue     = []
	reachable = []

	for neighbor, weight in G[src]:
		queue.append((weight, neighbor))

	heapq.heapify(queue)

	while queue:
		dist, node = heapq.heappop(queue)

		if node.islower() and node not in mykeys:
			reachable.append((node, dist))
			continue

		if node.lower() not in mykeys:
			continue

		for neighbor, weight in G[node]:
			new_dist = dist + weight

			if new_dist < distance[neighbor]:
				distance[neighbor] = new_dist
				heapq.heappush(queue, (new_dist, neighbor))

	return reachable

@lru_cache(2**20)
def explore(sources, n_find, mykeys=frozenset()):
	if n_find == 0:
		return 0

	best = INFINITY

	for src in sources:
		for k, d in reachable_keys(src, mykeys):
			dist = d + explore(sources.replace(src, k), n_find - 1, mykeys | {k})

			if dist < best:
				best = dist

	return best

def find_adjacent(grid, src):
	visited = {src}
	queue   = deque()
	found   = []

	for n in neighbors4(grid, *src):
		queue.append((1, n))

	while queue:
		dist, node = queue.popleft()

		if node not in visited:
			visited.add(node)

			cell = grid[node[0]][node[1]]

			if 'a' <= cell <= 'z' or 'A' <= cell <= 'Z':
					found.append((cell, dist))
					continue

			for neighbor in filter(lambda n: n not in visited, neighbors4(grid, *node)):
				queue.append((dist + 1, neighbor))

	return found

def build_graph(grid):
	graph    = {}
	startpos = None

	for r, row in enumerate(grid):
		for c, cell in enumerate(row):
			if cell not in '#.':
				graph[cell] = find_adjacent(grid, (r, c))

				if cell == '@':
					startpos = (r, c)

	return graph, startpos


advent.setup(2019, 18)
fin  = advent.get_input()
maze = tuple(list(l.strip()) for l in fin)

G, startpos = build_graph(maze)
total_keys  = sum(node.islower() for node in G)
min_steps   = explore('@', total_keys)

advent.print_answer(1, min_steps)


for r, c in neighbors4(maze, *startpos):
	maze[r][c] = '#'

startr, startc = startpos
maze[startr][startc] = '#'
maze[startr - 1][startc - 1] = '1'
maze[startr + 1][startc - 1] = '2'
maze[startr + 1][startc + 1] = '3'
maze[startr - 1][startc + 1] = '4'

distance_for_keys.cache_clear()
explore.cache_clear()
reachable_keys.cache_clear()

G, _      = build_graph(maze)
min_steps = explore('1234', total_keys)

advent.print_answer(2, min_steps)
