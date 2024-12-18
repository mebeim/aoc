#!/usr/bin/env python3

import sys
from collections import deque


def neighbors(grid, r, c):
	target = grid[r][c] + 1

	for dr, dc in ((0, 1), (0, -1), (1, 0), (-1, 0)):
		rr = r + dr
		cc = c + dc

		if 0 <= rr < len(grid) and 0 <= cc < len(grid[0]) and grid[rr][cc] == target:
			yield (rr, cc)


def dfs_count_reachable_9s(grid, r, c):
	q = deque([(r, c)])
	seen = set()
	total = 0

	while q:
		rc = q.pop()
		if rc in seen:
			continue

		seen.add(rc)
		r, c = rc
		total += grid[r][c] == 9
		q.extend(neighbors(grid, r, c))

	return total


def dfs_count_paths_to_9s(grid, r, c):
	# We don't need a visited set as we can only move to neighboring cells with
	# higher values, so it's impossible to visit the same cell twice on the same
	# path. It is however possible to visit it twice on different paths, which
	# is what we want.
	q = deque([(r, c)])
	total = 0

	while q:
		r, c = q.pop()
		total += grid[r][c] == 9
		q.extend(neighbors(grid, r, c))

	return total


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

grid = [list(map(int, line.strip())) for line in fin]
total1 = total2 = 0

for r, row in enumerate(grid):
	for c, x in enumerate(row):
		if x != 0:
			continue

		total1 += dfs_count_reachable_9s(grid, r, c)
		total2 += dfs_count_paths_to_9s(grid, r, c)

print('Part 1:', total1)
print('Part 2:', total2)
