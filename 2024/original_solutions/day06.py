#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 6)
fin = advent.get_input()

grid = read_char_matrix(fin)
ans1 = ans2 = 0

for r, row in enumerate(grid):
	for c, char in enumerate(row):
		if char == '^':
			startpos = r, c


def calc(grid, startpos):
	r, c = startpos
	dr, dc = -1, 0
	seen = set()

	while 1:
		# oob?
		if not (0 <= r < len(grid) and 0 <= c < len(grid[0])):
			break

		# hit a wall?
		if grid[r][c] == '#':
			r -= dr
			c -= dc
			dr, dc = dc, -dr
			continue

		k = (r, c, dr, dc)
		if k in seen:
			return True

		seen.add(k)
		r += dr
		c += dc

	return False


r, c = startpos
dr, dc = -1, 0
seen = set()
history = []

while 1:
	seen.add((r, c))
	history.append((r, c, dr, dc))

	if not (0 <= r + dr < len(grid) and 0 <= c + dc < len(grid[0])):
		break

	if grid[r + dr][c + dc] == '#':
		dr, dc = dc, -dr

	r += dr
	c += dc

ans1 = len(seen)
advent.print_answer(1, ans1)


prev = None

for r, row in enumerate(grid):
	for c, char in enumerate(row):
		if (r, c) not in seen or (r, c) == startpos:
			continue

		if prev is not None:
			grid[prev[0]][prev[1]] = '.'

		grid[r][c] = '#'
		prev = r, c
		ans2 += calc(grid, startpos)

# 1995 wrong
advent.print_answer(2, ans2)
