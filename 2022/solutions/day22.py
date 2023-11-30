#!/usr/bin/env python3

import sys
from functools import lru_cache

WALL, FREE, EMPTY = '#. '
RIGHT, DOWN, LEFT, UP = range(4)

DIRMAP = [
	(0, 1),
	(1, 0),
	(0, -1),
	(-1, 0),
]

FACES = (
	(1  , 50 , 51 , 100),
	(1  , 50 , 101, 150),
	(51 , 100, 51 , 100),
	(101, 150, 1  , 50 ),
	(101, 150, 51 , 100),
	(151, 200, 1  , 50 )
)

@lru_cache()
def leftmost_col(r):
	row = grid[r]
	return next(c for c in range(WIDTH) if row[c] != EMPTY)

@lru_cache()
def rightmost_col(r):
	row = grid[r]
	return next(c for c in range(WIDTH - 1, -1, -1) if row[c] != EMPTY)

@lru_cache()
def top_row(c):
	return next(r for r in range(HEIGHT) if grid[r][c] != EMPTY)

@lru_cache()
def bottom_row(c):
	return next(r for r in range(HEIGHT - 1, -1, -1) if grid[r][c] != EMPTY)

def step_grid(r, c, direction):
	dr, dc = DIRMAP[direction]
	r += dr
	c += dc

	if grid[r][c] == EMPTY:
		if direction == RIGHT:
			c = leftmost_col(r)
		elif direction == LEFT:
			c = rightmost_col(r)
		elif direction == DOWN:
			r = top_row(c)
		else:
			r = bottom_row(c)

	return r, c, direction

def face(r, c):
	for face_id, (rmin, rmax, cmin, cmax) in enumerate(FACES, 1):
		if rmin <= r <= rmax and cmin <= c <= cmax:
			return face_id, r - rmin + 1, c - cmin + 1

def step_cube(r, c, direction):
	dr, dc = DIRMAP[direction]
	newr = r + dr
	newc = c + dc

	if grid[newr][newc] != EMPTY:
		return newr, newc, direction

	face_id, fr, fc = face(r, c)

	if face_id == 1:
		if direction == UP:         # face 6 going right
			return fc + 150, 1, RIGHT
		# direction == LEFT        -> face 4 going right
		return (51 - fr) + 100, 1, RIGHT

	if face_id == 2:
		if direction == UP:         # face 6 going up
			return 200, fc, UP
		if direction == DOWN:       # face 3 going left
			return fc + 50, 100, LEFT
		# direction == RIGHT       -> face 5 going left
		return (51 - fr) + 100, 100, LEFT

	if face_id == 3:
		if direction == LEFT:       # face 4 going down
			return 101, fr, DOWN
		# direction == RIGHT       -> face 2 going up
		return 50, fr + 100, UP

	if face_id == 4:
		if direction == UP:         # face 3 going right
			return fc + 50, 51, RIGHT
		# direction == LEFT        -> face 1 going right
		return (51 - fr), 51, RIGHT

	if face_id == 5:
		if direction == RIGHT:      # face 2 going left
			return (51 - fr), 150, LEFT
		# direction == DOWN        -> face 6 going left
		return fc + 150, 50, LEFT

	# face_id == 6
	if direction == LEFT:           # face 1 going down
		return 1, fr + 50, DOWN
	if direction == RIGHT:          # face 5 going up
		return 150, fr + 50, UP
	else: # direction == DOWN      -> face 2 going down
		return 1, fc + 100, DOWN

def walk(grid, moves, step=step_grid):
	r = 1
	c = grid[1].index(FREE)
	d = RIGHT

	for move in moves:
		if move == 'L':
			d = (d - 1) % 4
		elif move == 'R':
			d = (d + 1) % 4
		else:
			for _ in range(move):
				newr, newc, newd = step(r, c, d)
				if grid[newr][newc] == WALL:
					break

				r, c, d = newr, newc, newd

	return 1000 * r + 4 * c + d


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

grid  = fin.read().splitlines()
moves = grid[-1]
grid  = grid[:-2]

HEIGHT, WIDTH = len(grid), max(map(len, grid))

for i in range(HEIGHT):
	grid[i] = EMPTY + grid[i].ljust(WIDTH, EMPTY) + EMPTY

HEIGHT += 2
WIDTH  += 2
grid = [EMPTY * WIDTH] + grid + [EMPTY * WIDTH]

moves = moves.replace('R', ' R ').replace('L', ' L ').split()
moves = tuple(map(lambda m: m if m in 'LR' else int(m), moves))

answer = walk(grid, moves)
print('Part 1:', answer)

answer = walk(grid, moves, step_cube)
print('Part 2:', answer)
