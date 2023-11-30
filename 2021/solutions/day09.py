#!/usr/bin/env python3

import sys
from collections import deque

def neighbors4(r, c, h, w):
	for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
		rr, cc = (r + dr, c + dc)
		if 0 <= rr < h and 0 <= cc < w:
			yield (rr, cc)

def component_size(grid, src, h, w):
	queue   = deque([src])
	visited = set()

	while queue:
		rc = queue.popleft()
		if rc in visited:
			continue

		visited.add(rc)

		for nr, nc in neighbors4(*rc, h, w):
			if grid[nr][nc] != 9 and (nr, nc) not in visited:
				queue.append((nr, nc))

	return len(visited)


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

lines = map(str.rstrip, fin)
grid  = tuple(tuple(map(int, row)) for row in lines)
h, w  = len(grid), len(grid[0])
total = 0
sinks = []

for r, row in enumerate(grid):
	for c, cell in enumerate(row):
		if all(grid[nr][nc] > cell for nr, nc in neighbors4(r, c, h, w)):
			sinks.append((r, c))
			total += cell + 1

print('Part 1:', total)


sizes  = map(lambda s: component_size(grid, s, h, w), sinks)
sizes  = sorted(sizes, reverse=True)
answer = sizes[0] * sizes[1] * sizes[2]

print('Part 2:', answer)
