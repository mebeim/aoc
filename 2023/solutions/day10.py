#!/usr/bin/env python3

import sys
from itertools import count

def add(ra, ca, rb, cb):
	return ra + rb, ca + cb

def find_start(grid):
	for r, row in enumerate(grid):
		for c, char in enumerate(row):
			if char == 'S':
				return r, c

def follow_pipes(grid, start_r, start_c):
	U, D, L, R = directions = ((-1, 0), (1, 0), (0, -1), (0, 1))
	possible_pipes = ('|F7', '|LJ', '-FL', '-J7')
	matches = ()

	for (dr, dc), pipes in zip(directions, possible_pipes):
		r, c = start_r + dr, start_c + dc

		if grid[r][c] in pipes:
			matches += ((dr, dc),)

	if   matches == (U, D): start_pipe = '|'
	elif matches == (L, R): start_pipe = '-'
	elif matches == (U, L): start_pipe = 'J'
	elif matches == (U, R): start_pipe = 'L'
	elif matches == (D, L): start_pipe = '7'
	else: start_pipe = 'F'

	r, c = start_r, start_c
	dr, dc = matches[0]
	seen = set([(r, c)])

	for steps in count(1):
		r, c = r + dr, c + dc
		pipe = grid[r][c]
		seen.add((r, c))

		if pipe in 'L7':
			dr, dc = dc, dr
		elif pipe in 'FJ':
			dr, dc = -dc, -dr
		elif pipe == 'S':
			break

	grid[start_r][start_c] = start_pipe
	return seen, steps

def inner_area(grid, main_loop):
	area = 0

	for r, row in enumerate(grid):
		inside = False

		for c, cell in enumerate(row):
			if (r, c) not in main_loop:
				area += inside
			else:
				inside = inside ^ (cell in '|F7')

	return area


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

grid = list(map(list, map(str.rstrip, fin)))
main_loop, loop_len = follow_pipes(grid, *find_start(grid))
max_pipe_distance = loop_len // 2
print('Part 1:', max_pipe_distance)

area = inner_area(grid, main_loop)
print('Part 2:', area)
