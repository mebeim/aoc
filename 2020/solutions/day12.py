#!/usr/bin/env python3

from utils import advent

LEFT, RIGHT = 'LR'
NORTH, SOUTH, EAST, WEST = 'NSEW'

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

x, y = 0, 0
dx, dy = 1, 0 # start facing EAST

for cmd, n in commands:
	if cmd == 'F':
		x += dx * n
		y += dy * n
	elif cmd in 'LR':
		dx, dy = ROTMAP[cmd, n](dx, dy)
	else:
		x, y = MOVEMAP[cmd](x, y, n)

dist = abs(x) + abs(y)
advent.print_answer(1, dist)


x, y = 0, 0
dx, dy = 10, 1

for cmd, n in commands:
	if cmd == 'F':
		x += dx * n
		y += dy * n
	elif cmd in 'LR':
		dx, dy = ROTMAP[cmd, n](dx, dy)
	else:
		dx, dy = MOVEMAP[cmd](dx, dy, n) # only change from the above code

dist = abs(x) + abs(y)
advent.print_answer(2, dist)
