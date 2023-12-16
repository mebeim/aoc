#!/usr/bin/env python3

import sys
from collections import deque
from operator import itemgetter

def travel(grid, height, width, start=(0, 0), direction=(0, 1)):
	queue = deque([(*start, *direction)])
	seen  = set()

	while queue:
		r, c, dr, dc = queue.pop()

		while 0 <= r < height and 0 <= c < width and (r, c, dr, dc) not in seen:
			seen.add((r, c, dr, dc))
			cell = grid[r][c]

			if cell == '/':
				dr, dc = -dc, -dr
			elif cell == '\\':
				dr, dc = dc, dr
			elif cell == '-' and dr:
				dr, dc = 0, 1
				queue.append((r, c - 1, 0, -1))
			elif cell == '|' and dc:
				dr, dc = 1, 0
				queue.append((r - 1, c, -1, 0))

			r += dr
			c += dc

	return len(set(map(itemgetter(0, 1), seen)))


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1], 'r') if len(sys.argv) > 1 else sys.stdin

with fin:
	grid = fin.read().splitlines()

h = len(grid)
w = len(grid[0])

energized = travel(grid, h, w)
print('Part 1:', energized)


best = 0

for r in range(h):
	best = max(best, travel(grid, h, w, (r,     0), (0,  1)))
	best = max(best, travel(grid, h, w, (r, w - 1), (0, -1)))

for c in range(w):
	best = max(best, travel(grid, h, w, (    0, c), ( 1, 0)))
	best = max(best, travel(grid, h, w, (h - 1, c), (-1, 0)))

print('Part 2:', best)
