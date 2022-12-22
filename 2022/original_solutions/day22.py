#!/usr/bin/env python3

from utils.all import *

def firstcol_fromleft(r):
	for c in range(WIDTH):
		if grid[r][c] != ' ':
			return c

def firstcol_fromright(r):
	for c in range(WIDTH - 1, -1, -1):
		if grid[r][c] != ' ':
			return c

def firstrow_fromtop(c):
	for r in range(HEIGHT):
		if grid[r][c] != ' ':
			return r

def firstrow_frombottom(c):
	for r in range(HEIGHT - 1, -1, -1):
		if grid[r][c] != ' ':
			return r

def face(r, c):
	assert r != 0 and c != 0 and r != HEIGHT - 1 and c != WIDTH - 1

	if r <= 50:
		if c <= 50:
			assert False
		elif c <= 100:
			return 1, r, c - 50
		else:
			return 2, r, c - 100
	elif r <= 100:
		if c <= 50:
			assert False
		elif c <= 100:
			return 3, r - 50, c - 50
		else:
			assert False
	elif r <= 150:
		if c <= 50:
			return 4, r - 100, c
		elif c <= 100:
			return 5, r - 100, c - 50
		else:
			assert False
	else:
		if c <= 50:
			return 6, r - 150, c
		else:
			assert False

def wrap(r, c, d):
	f, fr, fc = face(r, c)
	assert 1 <= f <= 6

	# eprint(f'WRAPPING from face {f} going {RDLU[d]} | r: {r} c: {c} fr: {fr} fc: {fc}')

	if f == 1:
		if d == UP: # -> face 6 going right
			newf = 6
			res = fc + 150, 1, RIGHT
		elif d == LEFT: # -> face 4 going right
			newf = 4
			res = (51 - fr) + 100, 1, RIGHT
		else:
			assert False, f'bad direction in face {f}: {RDLU[d]} | r: {r} c: {c} fr: {fr} fc: {fc}'
	elif f == 2:
		if d == UP: # -> face 6 up
			newf = 6
			res = 200, fc, UP
		elif d == DOWN: # -> face 3 left
			newf = 3
			res = fc + 50, 100, LEFT
		elif d == RIGHT: # -> face 5 left
			newf = 5
			res = (51 - fr) + 100, 100, LEFT
		else:
			assert False, f'bad direction in face {f}: {RDLU[d]} | r: {r} c: {c} fr: {fr} fc: {fc}'
	elif f == 3:
		if d == LEFT: # -> face 4 down
			newf = 4
			res = 101, fr, DOWN
		elif d == RIGHT: # -> face 2 up
			newf = 2
			res = 50, fr + 100, UP
		else:
			assert False, f'bad direction in face {f}: {RDLU[d]} | r: {r} c: {c} fr: {fr} fc: {fc}'
	elif f == 4:
		if d == UP: # -> face 3 right
			newf = 3
			res = fc + 50, 51, RIGHT
		elif d == LEFT: # -> face 1 right
			newf = 1
			res = (51 - fr), 51, RIGHT
		else:
			assert False, f'bad direction in face {f}: {RDLU[d]} | r: {r} c: {c} fr: {fr} fc: {fc}'
	elif f == 5:
		if d == RIGHT: # -> face 2 left
			newf = 2
			res = (51 - fr), 150, LEFT
		elif d == DOWN: # -> face 6 left
			newf = 6
			res = fc + 150, 50, LEFT
		else:
			assert False, f'bad direction in face {f}: {RDLU[d]} | r: {r} c: {c} fr: {fr} fc: {fc}'
	else:
		if d == LEFT: # -> face 1 down
			newf = 1
			res = 1, fr + 50, DOWN
		elif d == RIGHT: # -> face 5 up
			newf = 5
			res = 150, fr + 50, UP
		elif d == DOWN: # -> face 2 down
			newf = 2
			res = 1, fc + 100, DOWN
		else:
			assert False, f'bad direction in face {f}: {RDLU[d]} | r: {r} c: {c} fr: {fr} fc: {fc}'

	f, fr, fc = face(res[0], res[1])
	# eprint(f'WRAP       to face {f} going {RDLU[res[2]]} | r: {res[0]} c: {res[1]} fr: {fr} fc: {fc}')
	assert f == newf, 'New face seems wrong!'
	return res


advent.setup(2022, 22)
fin = advent.get_input()
grid = []

for line in fin:
	line = line.rstrip('\n')
	if not line:
		break

	grid.append(line)


WIDTH = max(map(len, grid))
HEIGHT = len(grid)

for i in range(len(grid)):
	grid[i] = list(' ' + grid[i].ljust(WIDTH, ' ') + ' ')

WIDTH += 2
HEIGHT += 2
grid = [list(' ' * WIDTH)] + grid + [list(' ' * WIDTH)]

moves = fin.readline().strip()
moves = moves.replace('R', ' R ').replace('L', ' L ').split()
R, C = 1, grid[1].index('.')
direction = 0

RIGHT, DOWN, LEFT, UP = range(4)
DIRMAP = [
	(0, 1),
	(1, 0),
	(0, -1),
	(-1, 0),
]

CURSOR = '>v<^'
RDLU = 'RDLU'

for i, move in enumerate(moves):
	if i % 2 == 0:
		n = int(move)
		dr, dc = DIRMAP[direction]

		for _ in range(n):
			newr = R + dr
			newc = C + dc

			if grid[newr][newc] == ' ':
				if direction == RIGHT:
					newc = firstcol_fromleft(newr)
				elif direction == LEFT:
					newc = firstcol_fromright(newr)
				elif direction == DOWN:
					newr = firstrow_fromtop(newc)
				elif direction == UP:
					newr = firstrow_frombottom(newc)

			if grid[newr][newc] == '#':
				break

			R, C = newr, newc
			# debug
			# grid[R][C] = CURSOR[direction]
	else:
		if move == 'R':
			direction = (direction + 1) % 4
		else:
			direction = (direction - 1) % 4

		# debug
		# grid[R][C] = CURSOR[direction]

	# dump_char_matrix(grid)
	# eprint('-' * 100)

ans = 1000 * R + 4 * C + direction
advent.print_answer(1, ans)


R, C = 1, grid[1].index('.')
direction = 0

for i, move in enumerate(moves):
	if i % 2 == 0:
		n = int(move)

		for _ in range(n):
			dr, dc = DIRMAP[direction]
			newr = R + dr
			newc = C + dc
			newd = direction

			if grid[newr][newc] == ' ':
				newr, newc, newd = wrap(R, C, direction)

			if grid[newr][newc] == '#':
				break

			R, C, direction = newr, newc, newd

			# grid[R][C] = 'o'
			# grid[R][C] = CURSOR[direction]
			# dump_char_matrix(grid)
	else:
		if move == 'R':
			direction = (direction + 1) % 4
		else:
			direction = (direction - 1) % 4

		# grid[R][C] = CURSOR[direction]
		# dump_char_matrix(grid)

ans = 1000 * R + 4 * C + direction
advent.print_answer(2, ans)
