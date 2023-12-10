#!/usr/bin/env python3

from utils.all import *

def check_bounds(grid, *lst):
	h, w = len(grid), len(grid[0])
	for r, c in lst:
		if 0 <= r < h and 0 <= c < w:
			yield r, c

def neighbors(grid, r, c, skipdot=False):
	x = grid[r][c]

	# | is a vertical pipe connecting north and south.
	# - is a horizontal pipe connecting east and west.
	# L is a 90-degree bend connecting north and east.
	# J is a 90-degree bend connecting north and west.
	# 7 is a 90-degree bend connecting south and west.
	# F is a 90-degree bend connecting south and east.
	if x == '|': return check_bounds(grid, (r - 1, c), (r + 1, c))
	if x == '-': return check_bounds(grid, (r, c - 1), (r, c + 1))
	if x == 'L': return check_bounds(grid, (r - 1, c), (r, c + 1))
	if x == 'J': return check_bounds(grid, (r - 1, c), (r, c - 1))
	if x == '7': return check_bounds(grid, (r + 1, c), (r, c - 1))
	if x == 'F': return check_bounds(grid, (r + 1, c), (r, c + 1))
	# . is ground; there is no pipe in this tile.
	if x == '.': assert skipdot, (r, c, 'this is a dot')
	return ()

def explore(grid, r, c):
	q = deque([(0, r, c)])
	seen = set()
	dists = defaultdict(lambda: INFINITY)

	while q:
		d, r, c = q.popleft()
		dists[r,c] = min(dists[r,c], d)
		if (r,c) in seen:
			continue

		seen.add((r,c))
		q.extend((d + 1, *n) for n in neighbors(grid, r, c))

	return seen, dists

def dump_readable(grid):
	readable_grid = []
	tbl = str.maketrans('|-LJ7F', '│─└┘┐┌')
	for row in grid:
		readable_grid.append(''.join(row).translate(tbl))

	dump_char_matrix(readable_grid)

def flood(grid, r, c):
	q = deque([(r, c)])
	seen = set()

	while q:
		r, c = q.popleft()
		if (r,c) in seen or grid[r][c] != '.':
			continue

		seen.add((r,c))
		q.extend(neighbors4(grid, r, c))

	return seen

def follow_loop(grid, r, c):
	assert grid[r][c] == '|', 'Follow from a vertical pipe pls'

	up, down, left, right = Vec(-1, 0), Vec(1, 0), Vec(0, -1), Vec(0, 1)
	dirname = {up: 'up', down: 'down', left: 'left', right: 'right'}
	dirmap = {
		(down, '|'): down ,
		(down, 'L'): right,
		(down, 'J'): left ,

		(up, '|'): up   ,
		(up, 'F'): right,
		(up, '7'): left ,

		(right, '-'): right,
		(right, 'J'): up   ,
		(right, '7'): down ,

		(left, '-'): left,
		(left, 'L'): up  ,
		(left, 'F'): down,
	}

	inoutmap = {
		up   : (left, right),
		down : (right, left),
		left : (down, up),
		right: (up, down),
	}

	start = pos = Vec(r, c)
	direction = down
	dir_inside, dir_outside = inoutmap[direction]

	while 1:
		# print(pos, dirname[direction].ljust(6), 'I', dirname[dir_inside].ljust(6), 'O', dirname[dir_outside])

		# Mark outside and inside
		new_inside  = flood(grid, *(pos + dir_inside))
		new_outside = flood(grid, *(pos + dir_outside))

		for rr, cc in new_inside:
			assert grid[rr][cc] in '.I'
			grid[rr][cc] = 'I'

		for rr, cc in new_outside:
			assert grid[rr][cc] in '.O'
			grid[rr][cc] = 'O'

		# Step in the direction
		pos  = pos + direction
		pipe = grid[pos.r][pos.c]
		# grid[pos.r][pos.c] = 'x'

		# Change direction if needed
		newdir = dirmap[direction, pipe]
		newdir_inside, newdir_outside = inoutmap[newdir]

		if direction != newdir:
			pi = po = None

			# Encountered a bend... mark tricky cells pointing away from bend
			if (direction, newdir) == (up, right):     # ┌
				pi = pos + left
			elif (direction, newdir) == (up, left):    # ┐
				po = pos + right
			elif (direction, newdir) == (down, right): # └
				po = pos + left
			elif (direction, newdir) == (down, left):  # ┘
				pi = pos + right
			elif (direction, newdir) == (right, up):   # ┘
				po = pos + down
			elif (direction, newdir) == (right, down): # ┐
				pi = pos + up
			elif (direction, newdir) == (left, up):    # └
				pi = pos + down
			elif (direction, newdir) == (left, down):  # ┌
				po = pos + up

			if pi:
				if grid[pi.r][pi.c] == '.':
					grid[pi.r][pi.c] = 'I'
			if po:
				if grid[po.r][po.c] == '.':
					grid[po.r][po.c] = 'O'

		direction = newdir
		dir_inside = newdir_inside
		dir_outside = newdir_outside

		if pos == start:
			break


advent.setup(2023, 10)
fin = advent.get_input()

grid = read_char_matrix(fin)
start = None
# dump_readable(grid)

for r, row in enumerate(grid):
	for c, char in enumerate(row):
		if char == 'S':
			conn = ()
			for nr, nc in neighbors4(grid, r, c):
				for xr, xc in neighbors(grid, nr, nc, skipdot=True):
					if xr == r and xc == c:
						conn += ((nr, nc),)

			if   set(conn) == set(((r - 1, c), (r + 1, c))): grid[r][c] = '|'
			elif set(conn) == set(((r, c - 1), (r, c + 1))): grid[r][c] = '-'
			elif set(conn) == set(((r - 1, c), (r, c + 1))): grid[r][c] = 'L'
			elif set(conn) == set(((r - 1, c), (r, c - 1))): grid[r][c] = 'J'
			elif set(conn) == set(((r + 1, c), (r, c - 1))): grid[r][c] = '7'
			elif set(conn) == set(((r + 1, c), (r, c + 1))): grid[r][c] = 'F'
			else:
				assert False, 'Cannot determine S pipe type: ' + repr(conn) + ' coords ' + repr((r, c))

			# print('S pipe:', grid[r][c])
			start = (r, c)


pipes, dists = explore(grid, *start)
ans = max(dists.values())

advent.print_answer(1, ans)


# Remove irrelevant pipes
for r, row in enumerate(grid):
	for c, char in enumerate(row):
		if (r, c) not in pipes:
			grid[r][c] = '.'

follow_loop(grid, *start)
# dump_readable(grid)

marker = 'I'
# Did i get it wrong? 50/50 chance
if grid[0][0] == 'I':
	marker = 'O'

inside = 0
for row in grid:
	inside += sum(x == marker for x in row)

advent.print_answer(2, inside)
