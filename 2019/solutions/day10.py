#!/usr/bin/env python3

from utils import advent
from fractions import gcd
from math import atan2, pi as PI

def ray(ax, ay, bx, by):
	dx, dy = bx - ax, by - ay
	div = abs(gcd(dx, dy))
	return dx//div, dy//div

def manhattan(ax, ay, bx, by):
	return abs(bx - ax) + abs(by - ay)

def angle(ax, ay, bx, by):
	rad = atan2(by-ay, bx-ax) + PI
	rad = rad % (2*PI) - PI/2
	return rad if rad >= 0 else 2*PI + rad


advent.setup(2019, 10)
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
	lines_of_sight = set()

	for a in asteroids:
		if a == src:
			continue

		lines_of_sight.add(ray(*src, *a))

	in_sight = len(lines_of_sight)
	if in_sight > max_in_sight:
		max_in_sight = in_sight
		station = src

advent.print_answer(1, max_in_sight)


closest = {}
target = 200

# This part 2 solution assumes that max_in_sight is always >= target (200).
# I.E. the 200th asteroid is destroyed in the first rotation.
assert max_in_sight >= target

for a in asteroids:
	if a == station:
		continue

	r = ray(*station, *a)
	m = manhattan(*station, *a)

	if r not in closest or m < closest[r][1]:
		closest[r] = (a, m)

ordered = sorted(closest.values(), key=lambda am: angle(*station, *am[0]))
chosen_x, chosen_y = ordered[target - 1][0]
ans = 100 * chosen_x + chosen_y

advent.print_answer(2, ans)
