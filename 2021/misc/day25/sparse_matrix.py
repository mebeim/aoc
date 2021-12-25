#!/usr/bin/env python3

from itertools import count

def evolve(sea, h, w):
	for n in count(1):
		advance = []

		for r, c in filter(lambda k: sea[k] == '>', sea):
			newc = (c + 1) % w

			if (r, newc) not in sea:
				advance.append((r, c, newc))

		horiz_still = not advance

		for r, c, newc in advance:
			del sea[r, c]
			sea[r, newc] = '>'

		advance = []

		for r, c in filter(lambda k: sea[k] == 'v', sea):
			newr = (r + 1) % h

			if (newr, c) not in sea:
				advance.append((r, c, newr))

		if horiz_still and not advance:
			break

		for r, c, newr in advance:
			del sea[r, c]
			sea[newr, c] = 'v'

	return n


with open('input.txt') as fin:
	grid = fin.read().split()

h, w = len(grid), len(grid[0])
sea  = {}

for r, row in enumerate(grid):
	for c, cell in enumerate(row):
		if cell != '.':
			sea[r, c] = cell


ans = evolve(sea, h, w)
print('Part 1:', ans)
