#!/usr/bin/env python3

from collections import defaultdict

import sys

DIRMAP = {
	'>': ( 0,  1),
	'<': ( 0, -1),
	'v': ( 1,  0),
	'^': (-1,  0),
}

def evolve_blizzard(bliz, width, height):
	new = defaultdict(list)

	for (r, c), dirs in bliz.items():
		for dr, dc in dirs:
			new[(r + dr) % height, (c + dc) % width].append((dr, dc))

	return new

def neighbors(bliz, r, c, height, width):
	if r == 0 and c == 0:
		yield -1, 0
	elif r == height - 1 and c == width - 1:
		yield height, c

	for dr, dc in ((0, 1), (1, 0), (0, -1), (-1, 0)):
		rr, cc = r + dr, c + dc
		if 0 <= rr < height and 0 <= cc < width and (rr, cc) not in bliz:
			yield rr, cc

	if (r, c) not in bliz:
		yield r, c

def advance(bliz, positions, height, width):
	for pos in positions:
		yield from neighbors(bliz, *pos, height, width)

def bfs(bliz, src, dst, height, width):
	positions = {src}
	time = 0

	while dst not in positions:
		time += 1
		bliz = evolve_blizzard(bliz, width, height)
		positions = set(advance(bliz, positions, height, width))

	return time, bliz


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

grid = fin.read().splitlines()
bliz = defaultdict(list)

for r, row in enumerate(grid[1:-1]):
	for c, cell in enumerate(row[1:-1]):
		if cell in DIRMAP:
			bliz[r, c].append(DIRMAP[cell])

height, width = len(grid) - 2, len(grid[0]) - 2
src, dst = (-1, 0), (height, width - 1)

time, bliz = bfs(bliz, src, dst, height, width)
print('Part 1:', time)


time2, bliz = bfs(bliz, dst, src, height, width)
time3, _    = bfs(bliz, src, dst, height, width)
time += time2 + time3
print('Part 2:', time)
