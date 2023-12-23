#!/usr/bin/env python3

import sys
from collections import defaultdict, deque

def neighbors(grid, r, c, ignore_slopes):
	cell = grid[r][c]

	if ignore_slopes or cell == '.':
		for r, c in ((r + 1, c), (r - 1, c), (r, c + 1), (r, c - 1)):
			if grid[r][c] != '#':
				yield r, c
	elif cell == 'v': yield (r + 1, c)
	elif cell == '^': yield (r - 1, c)
	elif cell == '>': yield (r, c + 1)
	elif cell == '<': yield (r, c - 1)

def num_neighbors(grid, r, c, ignore_slopes):
	if ignore_slopes or grid[r][c] == '.':
		return sum(grid[r][c] != '#' for r, c in ((r + 1, c), (r - 1, c), (r, c + 1), (r, c - 1)))
	return 1

def is_node(grid, rc, src, dst, ignore_slopes):
	return rc == src or rc == dst or num_neighbors(grid, *rc, ignore_slopes) > 2

def adjacent_nodes(grid, rc, src, dst, ignore_slopes):
	q = deque([(rc, 0)])
	seen = set()

	while q:
		rc, dist = q.popleft()
		seen.add(rc)

		for n in neighbors(grid, *rc, ignore_slopes):
			if n in seen:
				continue

			if is_node(grid, n, src, dst, ignore_slopes):
				yield (n, dist + 1)
				continue

			q.append((n, dist + 1))

def graph_from_grid(grid, src, dst, ignore_slopes=False):
	g = defaultdict(list)
	q = deque([src])
	seen = set()

	while q:
		rc = q.popleft()
		if rc in seen:
			continue

		seen.add(rc)

		for n, weight in adjacent_nodes(grid, rc, src, dst, ignore_slopes):
			g[rc].append((n, weight))
			q.append(n)

	return g

def longest_path(g, cur, dst, distance=0, seen=set()):
	if cur == dst:
		return distance

	best = 0
	seen.add(cur)

	for neighbor, weight in g[cur]:
		if neighbor in seen:
			continue

		best = max(best, longest_path(g, neighbor, dst, distance + weight))

	seen.remove(cur)
	return best


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1], 'r') if len(sys.argv) > 1 else sys.stdin

grid = list(map(list, fin.read().splitlines()))
height, width = len(grid), len(grid[0])

grid[0][1] = '#'
grid[height - 1][width - 2] = '#'

src = (1, 1)
dst = (height - 2, width - 2)

g = graph_from_grid(grid, src, dst)
pathlen = longest_path(g, src, dst) + 2
print('Part 1:', pathlen)

g = graph_from_grid(grid, src, dst, ignore_slopes=True)
pathlen = longest_path(g, src, dst) + 2
print('Part 2:', pathlen)
