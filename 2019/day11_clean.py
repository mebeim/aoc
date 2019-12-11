#!/usr/bin/env python3

import advent
from lib.intcode import IntcodeVM
from collections import defaultdict

BLACK, WHITE = 0, 1
LEFT, RIGHT = 0, 1
NORTH, SOUTH, EAST, WEST = 'NSEW'

DIRMAP = {
	NORTH: (WEST, EAST),
	SOUTH: (EAST, WEST),
	EAST: (NORTH, SOUTH),
	WEST: (SOUTH, NORTH)
}

MOVEMAP = {
	NORTH: (-1, 0),
	SOUTH: (+1, 0),
	EAST: (0, +1),
	WEST: (0, -1)
}

def run_robot(robot, starting_color):
	pos       = (0, 0)
	curdir    = NORTH
	grid      = defaultdict(lambda: BLACK)
	grid[pos] = starting_color

	robot.reset()

	while True:
		out = robot.run([grid[pos]], n_out=2, resume=True)

		if not out:
			break

		color, turn = out
		grid[pos] = color
		curdir = DIRMAP[curdir][turn]
		dx, dy = MOVEMAP[curdir]
		pos = (pos[0] + dx, pos[1] + dy)

	return grid


advent.setup(2019, 11, dry_run=True)
fin = advent.get_input()

program = list(map(int, fin.read().split(',')))
robot = IntcodeVM(program)
grid = run_robot(robot, BLACK)
n_painted = len(grid)

assert n_painted == 2056
advent.submit_answer(1, n_painted)

grid = run_robot(robot, WHITE)
mini, minj = min(grid)
maxi, maxj = max(grid)
height = maxi - mini + 1
width  = maxj - minj + 1
pic    = [([' '] * width) for _ in range(height)]

for i in range(height):
	for j in range(width):
		if grid[mini + i, minj + j] == WHITE:
			pic[i][j] = '#'

pic = ''.join(''.join(x) for x in pic)

assert (pic ==
	'  ##  #    ###  #### ###    ## #### ###  '
	' #  # #    #  # #    #  #    #    # #  # '
	' #    #    ###  ###  #  #    #   #  #  # '
	' # ## #    #  # #    ###     #  #   ###  '
	' #  # #    #  # #    #    #  # #    #    '
	'  ### #### ###  #### #     ##  #### #    '
)

# Can't submit this as is, LOL
advent.submit_answer(2, 'GLBEPJZP')
