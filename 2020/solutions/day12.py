#!/usr/bin/env python3

from utils import advent

LEFT, RIGHT = 'LR'
NORTH, SOUTH, EAST, WEST = 'NSEW'

# New direction when turning 90 degrees LEFT or RIGHT based on current direction.
DIRMAP = {
    NORTH: {LEFT:  WEST, RIGHT:  EAST},
    SOUTH: {LEFT:  EAST, RIGHT:  WEST},
    EAST : {LEFT: NORTH, RIGHT: SOUTH},
    WEST : {LEFT: SOUTH, RIGHT: NORTH}
}

# Function to apply to move forward in a specific direction.
MOVEMAP = {
    NORTH: lambda x, y, n: (    x, y + n),
    SOUTH: lambda x, y, n: (    x, y - n),
    EAST : lambda x, y, n: (x + n,     y),
    WEST : lambda x, y, n: (x - n,     y)
}

# Function to apply to rotate around the origin.
ROTMAP = {
	( LEFT,  90): lambda x, y: (-y,  x),
	( LEFT, 180): lambda x, y: (-x, -y),
	( LEFT, 270): lambda x, y: ( y, -x),
	(RIGHT,  90): lambda x, y: ( y, -x),
	(RIGHT, 180): lambda x, y: (-x, -y),
	(RIGHT, 270): lambda x, y: (-y,  x),
}


advent.setup(2020, 12)
fin = advent.get_input()

commands = tuple(map(lambda l: (l[0], int(l[1:])), fin))
direction = EAST
x, y = 0, 0

for cmd, n in commands:
	if cmd == 'F':
		x, y = MOVEMAP[direction](x, y, n)
	elif cmd in 'LR':
		for _ in range(n // 90):
			direction = DIRMAP[direction][cmd]
	else:
		x, y = MOVEMAP[cmd](x, y, n)

dist = abs(x) + abs(y)
advent.print_answer(1, dist)


x, y = 0, 0
wx, wy = 10, 1

for cmd, n in commands:
	if cmd == 'F':
		x += wx * n
		y += wy * n
	elif cmd in 'LR':
		wx, wy = ROTMAP[cmd, n](wx, wy)
	else:
		wx, wy = MOVEMAP[cmd](wx, wy, n)

dist = abs(x) + abs(y)
advent.print_answer(2, dist)

