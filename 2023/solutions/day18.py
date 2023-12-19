#!/usr/bin/env python3

import sys
from itertools import tee

# https://docs.python.org/3/library/itertools.html#itertools.pairwise
def pairwise(iterable):
	a, b = tee(iterable)
	next(b, None)
	return zip(a, b)

def shoelace(vertices):
	area = 0
	for (r1, c1), (_, c2) in pairwise(vertices):
		area += r1 * (c2 - c1)

	return abs(area)

def solve(vertices, perimeter):
	area = shoelace(vertices)
	return area + perimeter // 2 + 1


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1], 'r') if len(sys.argv) > 1 else sys.stdin

dirmap = {
	'0': (0, 1), '1': (1, 0), '2': (0, -1), '3': (-1, 0),
	'R': (0, 1), 'D': (1, 0), 'L': (0, -1), 'U': (-1, 0),
}

vertices1 = []
vertices2 = []
perimeter1 = 0
perimeter2 = 0
r1 = c1 = r2 = c2 = 0

for line in fin:
	direction, steps1, hexval = line.split()
	steps1 = int(steps1)

	dr, dc = dirmap[direction]
	r1 += steps1 * dr
	c1 += steps1 * dc

	direction = hexval[-2]
	steps2 = int(hexval[2:-2], 16)
	dr, dc = dirmap[direction]
	r2 += steps2 * dr
	c2 += steps2 * dc

	vertices1.append((r1, c1))
	vertices2.append((r2, c2))
	perimeter1 += steps1
	perimeter2 += steps2

vertices1.append((0, 0))
vertices2.append((0, 0))

area1 = solve(vertices1, perimeter1)
print('Part 1:', area1)

area2 = solve(vertices2, perimeter2)
print('Part 2:', area2)
