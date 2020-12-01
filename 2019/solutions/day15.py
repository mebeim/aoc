#!/usr/bin/env python3

from utils import advent
from collections import deque
from lib.intcode import IntcodeVM

WALL, EMPTY, OXYGEN = 0, 1, 2
NORTH, SOUTH, WEST, EAST = 1, 2, 3, 4
CLOCKWISE = (None, EAST, WEST, NORTH, SOUTH)
COUNTER_CLOCKWISE = (None, WEST, EAST, SOUTH, NORTH)

MOVE_DELTA = {
	NORTH: (-1, 0),
	SOUTH: (+1, 0),
	EAST: (0, +1),
	WEST: (0, -1)
}

def neighbors4(maze, r, c):
	for pos in ((r+1, c), (r-1, c), (r, c+1), (r, c-1)):
		if pos in maze:
			yield pos

def check_move(vm, move):
	return vm.run([move], n_out=1, resume=True)[0]

def wall_follower(vm, startpos, startdir=NORTH):
	curpos, curdir = startpos, startdir
	maze = set()
	oxygen = None

	while True:
		newdir = CLOCKWISE[curdir]
		dr, dc = MOVE_DELTA[newdir]
		newpos = (curpos[0] + dr, curpos[1] + dc)
		cell = check_move(vm, newdir)

		if cell == WALL:
			dr, dc = MOVE_DELTA[curdir]
			newpos = (curpos[0] + dr, curpos[1] + dc)
			cell = check_move(vm, curdir)

			if cell == WALL:
				curdir = COUNTER_CLOCKWISE[curdir]
			else:
				if cell == OXYGEN:
					oxygen = newpos
				maze.add(newpos)
				curpos = newpos
		else:
			if cell == OXYGEN:
				oxygen = newpos
			maze.add(newpos)
			curpos = newpos
			curdir = newdir

		if curpos == startpos and curdir == startdir:
			break

	return maze, oxygen

def bfs_shortest(maze, src, dst):
	visited = set()
	queue = deque([(0, src)])

	while queue:
		dist, node = queue.popleft()

		if node == dst:
			return dist

		if node not in visited:
			visited.add(node)

			for n in filter(lambda n: n not in visited, neighbors4(maze, *node)):
				queue.append((dist + 1, n))

	return float('inf')

def bfs_farthest(maze, src):
	visited = set()
	queue = deque([(0, src)])

	while queue:
		dist, node = queue.popleft()

		if node not in visited:
			visited.add(node)

			for n in filter(lambda n: n not in visited, neighbors4(maze, *node)):
				queue.append((dist + 1, n))

	return dist


advent.setup(2019, 15)
fin = advent.get_input()

program = list(map(int, fin.read().split(',')))
vm = IntcodeVM(program)

startpos = (0, 0)
maze, oxygen = wall_follower(vm, startpos)
min_dist = bfs_shortest(maze, startpos, oxygen)
advent.print_answer(1, min_dist)

time = bfs_farthest(maze, oxygen)
advent.print_answer(2, time)
