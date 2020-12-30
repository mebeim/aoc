#!/usr/bin/env python3

from utils.all import *

LEFT, RIGHT = 0, 1
NORTH, SOUTH, EAST, WEST = 'NSEW'

# New direction turning LEFT or RIGHT based on current direction.
DIRMAP = {
    NORTH: (WEST, EAST),
    SOUTH: (EAST, WEST),
    EAST: (NORTH, SOUTH),
    WEST: (SOUTH, NORTH)
}

# Delta to move when facing a secific direction.
MOVEMAP = {
    NORTH: (0, 1),
    SOUTH: (0, -1),
    EAST: (1, 0),
    WEST: (-1, 0)
}

advent.setup(2020, 12)
fin = advent.get_input()

# fin = io.StringIO('''\
# F10
# N3
# F7
# R90
# F11
# ''')

# eprint(*fin, sep=''); fin.seek(0, 0)
timer_start()
lines = get_lines(fin)

def manhattan(xa, ya, xb, yb):
	return abs(xb - xa) + abs(yb - ya)

direction = EAST
x, y = (0, 0)

for l in lines:
	d, n = l[0], int(l[1:])
	if d == 'N':
		y += n
	elif d == 'S':
		y -= n
	elif d == 'E':
		x += n
	elif d == 'W':
		x -= n
	elif d == 'F':
		dx, dy = MOVEMAP[direction]
		x += dx * n
		y += dy * n
	elif d == 'R':
		while n >= 90:
			direction = DIRMAP[direction][RIGHT]
			n -= 90
	elif d == 'L':
		while n >= 90:
			direction = DIRMAP[direction][LEFT]
			n -= 90
	else:
		assert False, 'wtf'

# 	eprint(d, n, '--->', direction, x, y)

ans = manhattan(0, 0, x, y)
advent.print_answer(1, ans)


direction = EAST
x, y = (0, 0)
wx, wy = 10, 1
from math import pi as PI, cos, sin
for l in lines:
	d, n = l[0], int(l[1:])
	if d == 'N':
		wy += n
	elif d == 'S':
		wy -= n
	elif d == 'E':
		wx += n
	elif d == 'W':
		wx -= n
	elif d == 'F':
		x += wx * n
		y += wy * n
	elif d == 'R':
		t = {90: -PI/2, 180: -PI, 270: -3 * PI/2}
		t = t[n]
		xx = wx * cos(t) - wy * sin(t)
		yy = wx * sin(t) + wy * cos(t)
		wx = int(round(xx))
		wy = int(round(yy))
	elif d == 'L':
		t = {90: PI/2, 180: PI, 270: 3 * PI/2}
		t = t[n]
		xx = wx * cos(t) - wy * sin(t)
		yy = wx * sin(t) + wy * cos(t)
		wx = int(round(xx))
		wy = int(round(yy))
	else:
		assert False, 'wtf'

	# eprint(d, n, '--->', direction, x, y, '|', wx, wy)

ans2 = manhattan(0, 0, x, y)
advent.print_answer(2, ans2)
