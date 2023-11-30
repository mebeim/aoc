#!/usr/bin/env python3

import sys
from itertools import product, count
from lib.intcode import intcode_oneshot

def run(inp):
	return next(intcode_oneshot(program, inp))

def get_width(x, target):
	for top in count(0):
		if run((x, top)) == 1:
			break

	if run((x, top + target)) == 0:
		return 0, 0

	for bottom in count(top + target + 1):
		if run((x, bottom)) == 0:
			break

	y = bottom - target

	for width in count(1):
		if run((x + width, y)) == 0:
			break

	return width, y

def bin_search(lo, hi, target):
	best = None

	while hi - lo > 1:
		x = (lo + hi) // 2

		width, y = get_width(x, target)

		if width > target:
			hi = x
			best = (x, y)
		elif width < target:
			lo = x

	return best


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

program = list(map(int, fin.read().split(',')))
total = sum(map(run, product(range(50), range(50))))

print('Part 1:', total)


TARGET = 100
bestx, besty = bin_search(10, 9999, TARGET)

for x in range(bestx, bestx - 10, -1):
	width, y = get_width(x, TARGET)

	if width >= TARGET:
		bestx, besty = x, y

answer = bestx * 10000 + besty
print('Part 2:', answer)
