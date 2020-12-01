#!/usr/bin/env python3

from utils.all import *
from copy import deepcopy

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

orig_grid = get_char_matrix(fin)

# orig_grid = [
# 	list('....#'),
# 	list('#..#.'),
# 	list('#.?##'),
# 	list('..#..'),
# 	list('#....'),
# ]

def neighbors4(grid, r, c):
	for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
		rr, cc = (r + dr, c + dc)
		if 0 <= rr < len(grid) and 0 <= cc < len(grid[rr]):
			yield (rr, cc)

def recursive_cell(curgrid, rgrid, depth, r, c):
	alive = 0

	if depth + 1 in rgrid:
		grid_below = rgrid[depth + 1]

		if (r, c) == (2, 1): # left
			alive += sum(grid_below[i][0] == '#' for i in range(N))
			# alive += sum(curgrid[i][j] == '#' for i, j in ((1,1), (2,0), (3,1)))
		elif (r, c) == (1, 2): # up
			alive += sum(grid_below[0][i] == '#' for i in range(N))
			# alive += sum(curgrid[i][j] == '#' for i, j in ((1,1), (0,2), (1,3)))
		elif (r, c) == (2, 3): # right
			alive += sum(grid_below[i][MAX] == '#' for i in range(N))
			# alive += sum(curgrid[i][j] == '#' for i, j in ((1,3), (2,4), (3,3)))
		elif (r, c) == (3, 2): # down
			alive += sum(grid_below[MAX][i] == '#' for i in range(N))
			# alive += sum(curgrid[i][j] == '#' for i, j in ((3,1), (4,2), (3,3)))

	if depth - 1 in rgrid:
		grid_above = rgrid[depth - 1]

		if c == 0 and grid_above[2][1] == '#': # left
			alive += 1
		if r == 0 and grid_above[1][2] == '#': # up
			alive += 1
		if c == MAX and grid_above[2][3] == '#': # right
			alive += 1
		if r == MAX and grid_above[3][2] == '#': # down
			alive += 1

	for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
		rr, cc = (r + dr, c + dc)

		if 0 <= rr < N and 0 <= cc < N:
			if (r, c) == (2, 2):
				continue

			if curgrid[rr][cc] == '#':
				alive += 1

	if curgrid[r][c] == '#':
		if alive == 1:
			return '#'
		return '.'

	if alive == 1 or alive == 2:
		return '#'
	return '.'

def recursive_nextgen(curgrid, rgrid, depth):
	grid = deepcopy(curgrid)

	for r in range(N):
		for c in range(N):
			if (r, c) == (2, 2):
				continue

			cell = recursive_cell(curgrid, rgrid, depth, r, c)
			grid[r][c] = cell

	return grid


grid = deepcopy(orig_grid)
seen = set()
i = 1

while True:
	x = ''.join(''.join(r) for r in grid)
	if x in seen:
		break
	seen.add(x)

	newgrid = deepcopy(grid)

	for r, row in enumerate(grid):
		for c, cell in enumerate(row):
			alive = 0
			for nr, nc in neighbors4(grid, r, c):
				if grid[nr][nc] == '#':
					alive += 1

			if grid[r][c] == '#':
				if alive != 1:
					newgrid[r][c] = '.'
			else:
				if alive in (1,2):
					newgrid[r][c] = '#'

	# print(i)
	# i += 1
	# dump_char_matrix(newgrid)

	grid = deepcopy(newgrid)

p = 1
tot = 0
for r, row in enumerate(grid):
	for c, cell in enumerate(row):
		if cell == '#':
			tot += p
		p *= 2


# 8243663 wrong
# print(tot)
advent.submit_answer(1, tot)


N = 5
MAX = 4

empty_grid = [['.']*N for _ in range(N)]
empty_grid[2][2] = '?'

grid = deepcopy(orig_grid)
grid[2][2] = '?'

rgrid = {0: grid}

# eprint()
# eprint('='*10, 0, '='*10)
# eprint()
# for k, v in sorted(rgrid.items()):
# 	eprint('-'*10, k)
# 	dump_char_matrix(v)

for generation in range(1, 200+1):
	newrgrid = deepcopy(rgrid)

	prev_depths = tuple(rgrid.keys())
	d, D = min(prev_depths) - 1, max(prev_depths) + 1

	grid = recursive_nextgen(empty_grid, rgrid, d)
	# dump_char_matrix(grid)
	if any(any(x == '#' for x in row) for row in grid):
		newrgrid[d] = grid

	grid = recursive_nextgen(empty_grid, rgrid, D)
	# dump_char_matrix(grid)
	if any(any(x == '#' for x in row) for row in grid):
		newrgrid[D] = grid

	for depth in prev_depths:
		newrgrid[depth] = recursive_nextgen(rgrid[depth], rgrid, depth)

	rgrid = newrgrid

	# eprint()
	# eprint('='*10, generation, '='*10)
	# eprint()
	# for k, v in sorted(rgrid.items()):
	# 	eprint('-'*10, k)
	# 	dump_char_matrix(v)

bugs = 0
for grid in rgrid.values():
	bugs += sum(sum(c == '#' for c in row) for row in grid)

# print(bugs)
advent.submit_answer(2, bugs)
