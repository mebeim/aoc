#!/usr/bin/env python3

import sys
from itertools import repeat, starmap, chain
from collections import defaultdict

def autorange(a, b):
	'''Go from a to b in steps of +/-1 regardless if a > b or b > a'''
	if a > b:
		yield from range(a, b - 1, -1)
	yield from range(a, b + 1)

def horiz(ax, ay, bx, by):
	if ax == bx:
		yield from zip(repeat(ax), autorange(ay, by))
	elif ay == by:
		yield from zip(autorange(ax, bx), repeat(ay))

def diag(ax, ay, bx, by):
	if ax != bx and ay != by:
		yield from zip(autorange(ax, bx), autorange(ay, by))


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

lines = []
space = defaultdict(int)

for raw_line in fin:
	a, b = raw_line.split('->')
	ax, ay = map(int, a.split(','))
	bx, by = map(int, b.split(','))
	lines.append((ax, ay, bx, by))

for p in chain(*starmap(horiz, lines)):
	space[p] += 1

overlapping = sum(x > 1 for x in space.values())
print('Part 1:', overlapping)


for p in chain(*starmap(diag, lines)):
	space[p] += 1

overlapping = sum(x > 1 for x in space.values())
print('Part 2:', overlapping)
