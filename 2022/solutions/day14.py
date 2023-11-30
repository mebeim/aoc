#!/usr/bin/env python3

from operator import itemgetter

import sys

def autorange(a, b):
	return range(a, b + 1) if a <= b else range(a, b - 1, -1)

def range2d(a, b):
	ax, ay = a
	bx, by = b

	if ax == bx:
		for y in autorange(ay, by):
			yield ax, y
	else:
		for x in autorange(ax, bx):
			yield x, ay

def pour_sand(cave, maxy, floor=False, x=500, y=0):
	if y == maxy and not floor:
		return True

	if y <= maxy or not floor:
		newy = y + 1

		for newx in (x, x - 1, x + 1):
			if (newx, newy) not in cave and pour_sand(cave, maxy, floor, newx, newy):
				return True

	cave.add((x, y))
	return False


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

cave = set()

for line in fin:
	points = (tuple(map(int, p.split(','))) for p in line.split(' -> '))
	prev   = next(points)

	for cur in points:
		cave.update(range2d(prev, cur))
		prev = cur

rocks = len(cave)
maxy  = max(map(itemgetter(1), cave))

pour_sand(cave, maxy)
sand = len(cave) - rocks
print('Part 1:', sand)


pour_sand(cave, maxy, True)
sand = len(cave) - rocks
print('Part 2:', sand)
