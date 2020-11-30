#!/usr/bin/env python3

from utils import advent

import sys
import copy

advent.setup(2018, 13)
fin = advent.get_input()
# print(*fin)

##################################################

def kill(crashxy):
	for i, cart in enumerate(carts):
		if tuple(cart[:2]) == crashxy:
			carts.pop(i)
			break

def dump(crashxy=(-1,-1)):
	cartdict = dict((tuple(c[:2]), c[2]) for c in carts)

	for i, l in enumerate(matrix):
		for j, c in enumerate(l):
			if (i, j) == crashxy:
				sys.stdout.write('X')
			elif (i, j) in cartdict:
				sys.stdout.write(cartdict[i, j])
			else:
				sys.stdout.write(c)
		sys.stdout.write('\n')

def step(stop_at_first):
	# dump()

	cartset = set(tuple(c[:2]) for c in carts)
	dead = []

	for cart in sorted(carts):
		x, y, d, t = cart
		t = TURNS[t]

		cartset = set(tuple(c[:2]) for c in carts)
		# cartset.remove((x, y))

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
			# dump(loc)
			kill(loc)
			kill(loc)

			dead.append(loc)
			# cartset.remove(loc)

			if stop_at_first:
				return dead
		else:
			cartset.add(loc)

	return dead

matrix = list(map(lambda l: list(l.strip('\n')), fin))

# for l in matrix:
# 	print('..'+''.join(l)+'..')

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

original_carts = []

for i, l in enumerate(matrix):
	for j, c in enumerate(l):
		if c in DIRECTIONS:
			original_carts.append([i, j, c, 0])

			if c in '^v':
				matrix[i][j] = '|'
			else:
				matrix[i][j] = '-'

carts = copy.deepcopy(original_carts)

crashed = []
while not crashed:
	crashed = step(True)

assert len(crashed) == 1

ans = ','.join(map(str, crashed[0][::-1]))
advent.submit_answer(1, ans)


carts = copy.deepcopy(original_carts)

while len(carts) > 1:
	crashed = []
	while not crashed:
		crashed = step(False)

assert len(carts) == 1

ans2 = ','.join(map(str, carts[0][:2][::-1]))

advent.submit_answer(2, ans2)
