#!/usr/bin/env python3

import advent
from fractions import gcd
from math import atan2, pi as PI

def direction(ax, ay, bx, by):
	dx, dy = bx - ax, by - ay
	div = abs(gcd(dx, dy))
	return dx//div, dy//div

def manhattan(ax, ay, bx, by):
	return abs(bx - ax) + abs(by - ay)

def angle(ax, ay, bx, by):
	rad = atan2(by-ay, bx-ax) + PI
	rad = rad % (2*PI) - PI/2
	return rad if rad >= 0 else 2*PI + rad


advent.setup(2019, 10, dry_run=True)
fin = advent.get_input()

grid = [l.rstrip() for l in fin]
asteroids = set()

for y, row in enumerate(grid):
	for x, cell in enumerate(row):
		if cell == '#':
			asteroids.add((x, y))

station = None
max_in_sight = 0

for src in asteroids:
	directions = set()

	for a in asteroids:
		if a == src:
			continue

		directions.add(direction(*src, *a))

	in_sight = len(directions)
	if in_sight > max_in_sight:
		max_in_sight = in_sight
		station = src

assert max_in_sight == 292
advent.submit_answer(1, max_in_sight)

# This part 2 solution assumes that max_in_sight is always >= 200.
# I.E. the 200th asteroid is destroyed in the first rotation.

closest = {}
target = 200

for a in asteroids:
	if a == station:
		continue

	d = direction(*station, *a)
	m = manhattan(*station, *a)

	if d not in closest or m < closest[d][1]:
		closest[d] = (a, m)

ordered = sorted(closest.values(), key=lambda am: angle(*station, *am[0]))
chosen_x, chosen_y = ordered[target - 1][0]
ans = 100 * chosen_x + chosen_y

assert ans == 317
advent.submit_answer(2, ans)
