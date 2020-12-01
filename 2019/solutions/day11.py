#!/usr/bin/env python3

from utils import advent
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

def sparse_to_matrix(grid):
	minx = min(x for x, _ in grid)
	maxx = max(x for x, _ in grid)
	miny = min(y for _, y in grid)
	maxy = max(y for _, y in grid)

	height = maxx - minx + 1
	width  = maxy - miny + 1
	matrix = [([' '] * width) for _ in range(height)]

	for x in range(height):
		for y in range(width):
			if grid[minx + x, miny + y] == WHITE:
				matrix[x][y] = '#'

	return matrix

advent.setup(2019, 11)
fin = advent.get_input()

program = list(map(int, fin.read().split(',')))
robot = IntcodeVM(program)
grid = run_robot(robot, BLACK)
n_painted = len(grid)

advent.print_answer(1, n_painted)

grid = run_robot(robot, WHITE)
pic = sparse_to_matrix(grid)
pic = ''.join(''.join(x) + '\n' for x in pic)

# Can't really print this nicely, but whatever
advent.print_answer(2, '\n' + pic)
