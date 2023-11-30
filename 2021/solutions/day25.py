#!/usr/bin/env python3

import sys
from itertools import count

def evolve(grid):
	h, w  = len(grid), len(grid[0])
	steps = 0

	for steps in count(1):
		advance = []

		for r in range(h):
			for c in range(w):
				newc = (c + 1) % w

				if grid[r][c] == '>' and grid[r][newc] == '.':
					advance.append((r, c, newc))

		for r, c, newc in advance:
			grid[r][c]    = '.'
			grid[r][newc] = '>'

		horiz_still = not advance
		advance = []

		for r in range(h):
			for c in range(w):
				newr = (r + 1) % h

				if grid[r][c] == 'v' and grid[newr][c] == '.':
					advance.append((r, c, newr))

		if horiz_still and not advance:
			break

		for r, c, newr in advance:
			grid[r][c]    = '.'
			grid[newr][c] = 'v'

	return steps


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

grid = list(map(list, fin.read().split()))
ans  = evolve(grid)

print('Part 1:', ans)
