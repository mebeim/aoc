#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 11)
fin = advent.get_input()

# fin = io.StringIO('''\
# L.LL.LL.LL
# LLLLLLL.LL
# L.L.L..L..
# LLLL.LL.LL
# L.LL.LL.LL
# L.LLLLL.LL
# ..L.L.....
# LLLLLLLLLL
# L.LLLLLL.L
# L.LLLLL.LL
# ''')

# eprint(*fin, sep=''); fin.seek(0, 0)
timer_start()

orig_grid = get_char_matrix(fin)
grid = copy.deepcopy(orig_grid)

while 1:
	prevgrid = copy.deepcopy(grid)

	for r in range(len(grid)):
		for c in range(len(grid[r])):
			x = prevgrid[r][c]
			if x == '.':
				continue

			neigh = ''.join(prevgrid[rr][cc] for rr,cc in neighbors8(prevgrid, r, c, avoid=''))

			if x == 'L' and '#' not in neigh:
				grid[r][c] = '#'
			elif x == '#' and neigh.count('#') >= 4:
				grid[r][c] = 'L'

	# dump_char_matrix(grid)
	# eprint('---')
	if grid == prevgrid:
		break

	prevgrid = grid

ans = sum(l.count('#') for l in grid)
advent.print_answer(1, ans)

from itertools import count
def neighborswtf(grid, r, c):
	width  = len(grid)
	height = len(grid[0])

	# down
	for rr in range(r + 1, width):
		if grid[rr][c] != '.':
			yield grid[rr][c]
			break
	# up
	for rr in range(r - 1, -1, -1):
		if grid[rr][c] != '.':
			yield grid[rr][c]
			break
	# right
	for cc in range(c + 1, height):
		if grid[r][cc] != '.':
			yield grid[r][cc]
			break
	# left
	for cc in range(c - 1, -1, -1):
		if grid[r][cc] != '.':
			yield grid[r][cc]
			break

	for d in count(1):
		rr, cc = r + d, c + d
		if 0 <= rr < width and 0 <= cc < height:
			if grid[rr][cc] != '.':
				yield grid[rr][cc]
				break
		else:
			break

	for d in count(1):
		rr, cc = r - d, c - d
		if 0 <= rr < width and 0 <= cc < height:
			if grid[rr][cc] != '.':
				yield grid[rr][cc]
				break
		else:
			break

	for d in count(1):
		rr, cc = r - d, c + d
		if 0 <= rr < width and 0 <= cc < height:
			if grid[rr][cc] != '.':
				yield grid[rr][cc]
				break
		else:
			break

	for d in count(1):
		rr, cc = r + d, c - d
		if 0 <= rr < width and 0 <= cc < height:
			if grid[rr][cc] != '.':
				yield grid[rr][cc]
				break
		else:
			break

grid = copy.deepcopy(orig_grid)

# for _ in range(5):
while 1:
	prevgrid = copy.deepcopy(grid)

	for r in range(len(grid)):
		for c in range(len(grid[r])):
			x = prevgrid[r][c]
			if x == '.':
				continue

			neigh = ''.join(neighborswtf(prevgrid, r, c))

			if x == 'L' and '#' not in neigh:
				grid[r][c] = '#'
			elif x == '#' and neigh.count('#') >= 5:
				grid[r][c] = 'L'

	# dump_char_matrix(grid)
	# eprint('---')
	if grid == prevgrid:
		break

	prevgrid = grid

ans = sum(l.count('#') for l in grid)
advent.print_answer(2, ans)
