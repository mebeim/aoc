#!/usr/bin/env python3

from itertools import repeat

from utils.all import *

def loop(data):
	for i in count(0):
		yield data[i % len(data)]

def newrock(off, topy):
	r = []
	for dx, dy in off:
		r.append([dx + 2, (topy + dy + 4)])
	return r

def left(r):
	for i, (x, y) in enumerate(r):
		r[i] = (x - 1, y)

def right(r):
	for i, (x, y) in enumerate(r):
		r[i] = (x + 1, y)

def down(r):
	for i, (x, y) in enumerate(r):
		r[i] = (x, y - 1)

def collision(rock, direction):
	if direction == 'l':
		if any(x == 0 for x,_ in rock):
			# eprint('Collision L wall')
			return True

		for x, y in rock:
			if (x - 1, y) in space:
				# eprint('Collision L')
				return True
	elif direction == 'r':
		if any(x == 6 for x,_ in rock):
			# eprint('Collision R wall')
			return True

		for x, y in rock:
			if (x + 1, y) in space:
				# eprint('Collision R')
				return True
	elif direction == 'd':
		if any(y == 1 for _,y in rock):
			# eprint('Collision bottom')
			return True

		for x, y in rock:
			if (x, y - 1) in space:
				# eprint('Collision D')
				return True
	return False

def dump():
	res = ''
	for y in range(topy + 7, -1, -1):
		for x in range(7):
			if (x, y) in space:
				res += '#'
			elif (x, y) in rock:
				res += 'o'
			else:
				res += ' '
		res += '\n'

	# eprint(res)
	# eprint('-' * 20)


advent.setup(2022, 17)
DEBUG = 'debug' in map(str.lower, sys.argv)
fin = advent.get_input() if not DEBUG else io.StringIO('''\
>>><<><>><<<>><>>><<<>>><<<><<<>><>><<>>
''')

data = fin.read().strip()
timer_start()

offsets = [
	((0, 0), (1, 0), (2, 0), (3, 0)),
	((1, 0), (0, 1), (1, 1), (2, 1), (1, 2)),
	((0, 0), (1, 0), (2,0), (2, 1), (2, 2)),
	((0, 0), (0, 1), (0, 2), (0,3)),
	((0, 0), (1, 0), (0, 1), (1, 1))
]

moves = loop(data)
space = {(i, 0) for i in range(7)}
topy  = 0

for n in range(2022):
	# eprint('=' * 20, 'rock', n + 1, '=' * 30)
	rock = newrock(offsets[n % len(offsets)], topy)

	while 1:
		# eprint(rock)

		move = next(moves)
		if move == '<' and not collision(rock, 'l'):
			left(rock)
			# eprint('Move left', rock)
		elif move == '>' and not collision(rock, 'r'):
			right(rock)
			# eprint('Move right', rock)
		# else:
			# eprint('No lateral move')

		# dump()

		if collision(rock, 'd'):
			space.update(map(tuple, rock))
			topy = max(map(itemgetter(1), space))
			break

		down(rock)

		# eprint('Move down', rock)
		# dump()

advent.print_answer(1, topy)


moves = loop(data)
space = {(i, 0) for i in range(7)}
topy  = 0
previous = {}
n = 0
skipped = None
totrocks = 1000000000000
iteration = 0

while n < totrocks:
	# eprint('=' * 20, 'rock', n + 1, '=' * 30)
	rocktype = n % len(offsets)
	rock = newrock(offsets[rocktype], topy)

	while 1:
		move = next(moves)
		iteration += 1
		iteration %= len(data)

		if move == '<' and not collision(rock, 'l'):
			left(rock)
			# eprint('Move left', rock)
		elif move == '>' and not collision(rock, 'r'):
			right(rock)
			# eprint('Move right', rock)
		# else:
			# eprint('No lateral move')

		# dump()

		if collision(rock, 'd'):
			space.update(map(tuple, rock))
			topy = max(map(itemgetter(1), space))

			if skipped is None and topy > 200:
				topchunk = []
				for x, y in space:
					if y >= topy - 100:
						topchunk.append((x, topy - y))

				state = (tuple(sorted(topchunk)), iteration, rocktype)

				if state in previous:
					nn, yy = previous[state]
					deltay = topy - yy
					deltan = n - nn
					# eprint('pattern repeats every', deltan, 'rocks going up', deltay)
					# eprint('jump fom rock', n, 'to', totrocks - n)
					# 1963 to 999999998037

					steps = (totrocks - n) // deltan
					skipped = deltay * steps
					n += deltan * steps

				previous[state] = (n, topy)

			break

		down(rock)

		# eprint('Move down', rock)
		# dump()

	n += 1

topy += skipped

advent.print_answer(2, topy)
