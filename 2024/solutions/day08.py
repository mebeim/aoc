#!/usr/bin/env python3

import sys
from collections import defaultdict
from itertools import combinations, count


def antinodes(r1, c1, r2, c2):
	global HEIGHT, WIDTH

	r = 2 * r2 - r1
	c = 2 * c2 - c1
	if 0 <= r < HEIGHT and 0 <= c < WIDTH:
		yield r, c

	r = 2 * r1 - r2
	c = 2 * c1 - c2
	if 0 <= r < HEIGHT and 0 <= c < WIDTH:
		yield r, c


def points_on_line(r1, c1, r2, c2):
	global HEIGHT, WIDTH

	dr = r2 - r1
	dc = c2 - c1

	for mult in count(0):
		r = r1 + mult * dr
		c = c1 + mult * dc

		if 0 <= r < HEIGHT and 0 <= c < WIDTH:
			yield r, c
		else:
			break


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

grid = fin.read().splitlines()
HEIGHT, WIDTH = len(grid), len(grid[0])

frequencies = defaultdict(set)
points1 = set()
points2 = set()

for r, row in enumerate(grid):
	for c, cell in enumerate(row):
		if cell != '.':
			frequencies[cell].add((r, c))

for antennas in frequencies.values():
	for a, b in combinations(antennas, 2):
		points1.update(antinodes(*a, *b))
		points2.update(points_on_line(*a, *b))
		points2.update(points_on_line(*b, *a))

ans1 = len(points1)
print('Part 1:', ans1)

ans2 = len(points2)
print('Part 2:', ans2)
