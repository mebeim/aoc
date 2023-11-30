#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1], 'rb') if len(sys.argv) > 1 else sys.stdin.buffer

grid          = fin.read().splitlines()
height, width = len(grid), len(grid[0])
maxr, maxc    = height - 1, width - 1
visible       = height * 2 + width * 2 - 4
best          = 0

for r in range(1, maxr):
	row = grid[r]

	for c in range(1, maxc):
		tree = row[c]

		e = (tree > t for t in row[c + 1:])
		w = (tree > t for t in row[:c])
		s = (tree > grid[i][c] for i in range(r + 1, len(grid)))
		n = (tree > grid[i][c] for i in range(r - 1, -1, -1))

		if all(e) or all(w) or all(s) or all(n):
			visible += 1

print('Part 1:', visible)


for r in range(1, maxr):
	row = grid[r]

	for c in range(1, maxc):
		tree = row[c]

		for e in range(c + 1, width):
			if row[e] >= tree:
				break

		for w in range(c - 1, -1, -1):
			if row[w] >= tree:
				break

		for s in range(r + 1, height):
			if grid[s][c] >= tree:
				break

		for n in range(r - 1, -1, -1):
			if grid[n][c] >= tree:
				break

		score = (e - c) * (c - w) * (s - r) * (r - n)

		if score > best:
			best = score

print('Part 2:', best)
