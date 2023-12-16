#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 16)
fin = advent.get_input()
grid = read_char_matrix(fin)

U, D, L, R = ((-1, 0), (1, 0), (0, -1), (0, 1))

def travel(grid, start_r=0, start_c=0, start_d=R):
	height, width = len(grid), len(grid[0])
	beam = Vec(start_r, start_c)
	q = deque([(beam, start_d)])
	visited = set()
	seen = set()

	while q:
		beam, d = q.popleft()
		if beam.r < 0 or beam.c < 0 or beam.r >= height or beam.c >= width:
			continue

		if (beam, d) in visited:
			continue

		visited.add((beam, d))
		seen.add(beam)
		x = grid[beam.r][beam.c]

		if (d, x) in ((R, '/'), (L, '\\')):
			q.appendleft((beam + U, U))
		elif (d, x) in ((L, '/'), (R, '\\')):
			q.appendleft((beam + D, D))
		elif (d, x) in ((U, '/'), (D, '\\')):
			q.appendleft((beam + R, R))
		elif (d, x) in ((D, '/'), (U, '\\')):
			q.appendleft((beam + L, L))
		elif d in (U, D) and x == '-':
			q.appendleft((beam + L, L))
			q.appendleft((beam + R, R))
		elif d in (L, R) and x == '|':
			q.appendleft((beam + U, U))
			q.appendleft((beam + D, D))
		else:
			q.appendleft((beam + d, d))

	return len(seen)


ans1 = travel(grid)
advent.print_answer(1, ans1)


height, width = len(grid), len(grid[0])
best = 0

for r in range(height):
	best = max(best, travel(grid, r, 0, R))
	best = max(best, travel(grid, r, width - 1, L))

for c in range(width):
	best = max(best, travel(grid, 0, c, D))
	best = max(best, travel(grid, height - 1, c, U))

advent.print_answer(2, best)
