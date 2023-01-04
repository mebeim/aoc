#!/usr/bin/env python3

import re
from itertools import starmap, combinations

from utils import advent

def manhattan(ax, ay, bx, by):
	return abs(ax - bx) + abs(ay - by)

def diamond_segment(sx, sy, r):
	dist = abs(2000000 - sy)

	if dist <= r:
		return (sx - r + dist, sx + r - dist)

def invalid_spots(sensors):
	segments = iter(sorted(filter(None, starmap(diamond_segment, sensors))))
	start, end = next(segments)
	total = 0

	for s, e in segments:
		if s > end + 1:
			total += end - start + 1
			start, end = s, e
		else:
			end = max(end, e)

	return total + end - start + 1

def sides(sx, sy, r):
	r += 1
	yield -sx + sy + r # a/\b  a: y =  x - sx + sy + r + 1
	yield  sx + sy + r # /  \  b: y = -x + sx + sy + r + 1
	yield -sx + sy - r # \  /  c: y =  x - sx + sy - r - 1
	yield  sx + sy - r # d\/c  d: y = -x + sx + sy - r - 1

def intersect(a, b):
	x = (b - a) // 2
	return x, x + a

def candidates(s1, s2):
	a1, b1, c1, d1 = sides(*s1)
	a2, b2, c2, d2 = sides(*s2)
	yield intersect(a1, b2)
	yield intersect(a1, d2)
	yield intersect(c1, b2)
	yield intersect(c1, d2)
	yield intersect(a2, b1)
	yield intersect(a2, d1)
	yield intersect(c2, b1)
	yield intersect(c2, d1)

def missing_beacon(sensors):
	for s1, s2 in combinations(sensors, 2):
		for x, y in candidates(s1, s2):
			if x < 0 or x > 4000000 or y < 0 or y > 4000000:
				continue

			if all(manhattan(sx, sy, x, y) > r for sx, sy, r in sensors):
				return x, y


advent.setup(2022, 15)

exp = re.compile(r'-?\d+')
sensors = []
beacons_on_target = set()

with advent.get_input() as fin:
	for line in fin:
		sx, sy, bx, by = map(int, exp.findall(line))
		sensors.append((sx, sy, manhattan(sx, sy, bx, by)))

		if by == 2000000:
			beacons_on_target.add(bx)

answer = invalid_spots(sensors) - len(beacons_on_target)
advent.print_answer(1, answer)

x, y = missing_beacon(sensors)
answer = x * 4000000 + y
advent.print_answer(2, answer)
