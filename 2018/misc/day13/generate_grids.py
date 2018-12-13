#!/usr/bin/env python3

import os
import sys
import pickle

def kill(crashxy):
	for i, cart in enumerate(carts):
		if tuple(cart[:2]) == crashxy:
			carts.pop(i)
			break

def gen_grid(n, crashed):
	grid = [l[:] for l in matrix]

	for i in range(1, len(grid)-1):
		for j, c in enumerate(grid[i][1:-1], 1):
			if c == '/':
				if   grid[i][j-1] in '-+': grid[i][j] = '╯'
				elif grid[i][j+1] in '-+': grid[i][j] = '╭'
			elif c == '\\':
				if   grid[i][j-1] in '-+': grid[i][j] = '╮'
				elif grid[i][j+1] in '-+': grid[i][j] = '╰'

	for i in range(len(grid)):
		for j, c in enumerate(grid[i]):
			if c in GRID_CHARMAP:
				grid[i][j] = GRID_CHARMAP[c]

	for x, y, d, _ in carts:
		grid[x][y] = d

	for x, y in crashed:
		grid[x][y] = 'X'

	grid = list(map(lambda l: ''.join(l), grid))

	with open('grids/grid_{:03d}.pkl'.format(n), 'wb') as f:
		pickle.dump({
			'grid'   : grid,
			'carts'  : carts,
			'crashed': crashed
		}, f, protocol=4)

def step(stop_at_first):
	cartset = set(tuple(c[:2]) for c in carts)
	dead = set()

	for cart in sorted(carts):
		x, y, d, t = cart
		t = TURNS[t]

		cartset = set(tuple(c[:2]) for c in carts)

		assert matrix[x][y] != ' '

		if matrix[x][y] == RAILX:
			if d == DOWN:
				if   t == LEFT : cart[1] += 1; cart[2] = RIGHT
				elif t == RIGHT: cart[1] -= 1; cart[2] = LEFT
				else           : cart[0] += 1
			elif d == UP:
				if   t == LEFT : cart[1] -= 1; cart[2] = LEFT
				elif t == RIGHT: cart[1] += 1; cart[2] = RIGHT
				else           : cart[0] -= 1
			elif d == RIGHT:
				if   t == LEFT : cart[0] -= 1; cart[2] = UP
				elif t == RIGHT: cart[0] += 1; cart[2] = DOWN
				else           : cart[1] += 1
			elif d == LEFT:
				if   t == LEFT : cart[0] += 1; cart[2] = DOWN
				elif t == RIGHT: cart[0] -= 1; cart[2] = UP
				else           : cart[1] -= 1

			cart[3] = (cart[3] + 1) % 3
		elif matrix[x][y] in (RAILL, RAILR):
			rail = matrix[x][y]

			if d == DOWN:
				if rail == RAILL: cart[1] += 1; cart[2] = RIGHT
				else            : cart[1] -= 1; cart[2] = LEFT
			elif d == UP:
				if rail == RAILL: cart[1] -= 1; cart[2] = LEFT
				else            : cart[1] += 1; cart[2] = RIGHT
			elif d == RIGHT:
				if rail == RAILL: cart[0] += 1; cart[2] = DOWN
				else            : cart[0] -= 1; cart[2] = UP
			elif d == LEFT:
				if rail == RAILL: cart[0] -= 1; cart[2] = UP
				else            : cart[0] += 1; cart[2] = DOWN
		else:
			if d == DOWN:
				cart[0] += 1
			elif d == UP:
				cart[0] -= 1
			elif d == RIGHT:
				cart[1] += 1
			elif d == LEFT:
				cart[1] -= 1

		loc = tuple(cart[:2])

		if loc in cartset:
			kill(loc)
			kill(loc)

			dead.add(loc)

			if stop_at_first:
				return dead
		else:
			cartset.add(loc)

	return dead

###########################################################33

# fin = open('mebeim.in') # ~16k iterations
fin = open('cyphase.in') # ~10k iterations

matrix = list(map(lambda l: list(l.strip('\n')), fin))

assert all(len(x) == len(y) for x, y in zip(matrix[:-1], matrix[1:]))

UP       = '^'
DOWN     = 'v'
RIGHT    = '>'
LEFT     = '<'
STRAIGHT = '='
RAILR    = '/'
RAILL    = '\\'
RAILX    = '+'

DIRECTIONS = (UP, DOWN, RIGHT, LEFT)
TURNS      = (LEFT, STRAIGHT, RIGHT)

GRID_CHARMAP = {
	'-': '─',
	'|': '│',
	'+': '┼'
}

carts = []
for i, l in enumerate(matrix):
	for j, c in enumerate(l):
		if c in DIRECTIONS:
			carts.append([i, j, c, 0])

			if c in '^v':
				matrix[i][j] = '|'
			else:
				matrix[i][j] = '-'

if not os.path.isdir('grids'):
	os.mkdir('grids')

grid_no = 0
sys.stderr.write('Generating grid #{}...\r'.format(grid_no))
sys.stderr.flush()

gen_grid(grid_no, [])

crashed_so_far = set()

while len(carts) > 1:
	crashed = set()
	while not crashed:
		crashed = step(False)
		crashed_so_far = crashed_so_far.union(crashed)

		grid_no += 1
		sys.stderr.write('Generating grid #{}...\r'.format(grid_no))
		sys.stderr.flush()

		gen_grid(grid_no, crashed_so_far)

sys.stderr.write('Done! All grids generated.        \n')
