#!/usr/bin/env python3

import sys

MOVE_DX = {'U': 0, 'D':  0, 'R': 1, 'L': -1}
MOVE_DY = {'U': 1, 'D': -1, 'R': 0, 'L':  0}

def make_move(s):
	return s[0], int(s[1:])

def get_visited_and_steps(moves):
	p = (0, 0)
	cur_steps = 0
	visited = set()
	steps = {}

	for d, n in moves:
		for _ in range(n):
			p = (p[0] + MOVE_DX[d], p[1] + MOVE_DY[d])
			visited.add(p)
			cur_steps += 1

			if p not in steps:
				steps[p] = cur_steps

	return visited, steps

def manhattan(p):
	return abs(p[0]) + abs(p[1])


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin
lines = fin.readlines()

all_visited = []
all_steps = []

for l in lines:
	visited, steps = get_visited_and_steps(map(make_move, l.split(',')))
	all_visited.append(visited)
	all_steps.append(steps)

intersections = set.intersection(*all_visited)
min_distance = min(map(manhattan, intersections))
print('Part 1:', min_distance)

shortest_path = min(sum(l[p] for l in all_steps) for p in intersections)
print('Part 2:', shortest_path)
