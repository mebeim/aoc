#!/usr/bin/env python3

import sys
from re import findall
from collections import Counter
from dataclasses import dataclass
from math import prod

@dataclass
class Robot:
	x: int
	y: int
	vx: int
	vy: int


def quadrant(r):
	x = (r.x + r.vx * 100) % 101
	y = (r.y + r.vy * 100) % 103

	if x != 50 and y != 51:
		return x > 50, y > 51
	return None


def find_tree(robots):
	best = 0
	res = 0

	for time in range(1, 101 * 103):
		sparse = set()
		heuristic = 0

		for r in robots:
			r.x = (r.x + r.vx) % 101
			r.y = (r.y + r.vy) % 103
			sparse.add((r.x, r.y))

		for x, y in sparse:
			heuristic += (x + 1, y) in sparse

		if heuristic > best:
			best = heuristic
			res = time

	return res


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

ints = list(map(int, findall(r'-?\d+', fin.read())))
robots = list(Robot(*ints[i:i + 4]) for i in range(0, len(ints), 4))

total = prod(Counter(filter(None, map(quadrant, robots))).values())
print('Part 1:', total)

time = find_tree(robots)
print('Part 2:', time)
