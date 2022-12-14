#!/usr/bin/env python3

from utils.all import *

advent.setup(2022, 14)
fin = advent.get_input()
intmat = read_int_matrix(fin); fin.seek(0, 0)

ans = 0
rock = set()
sand = set()

def dump():
	res = ''
	for y in range(13):
		for x in range(490, 510):
			if (x, y) in rock:
				res += '#'
			elif (x, y) in sand:
				res += 'o'
			else:
				res += '.'
		res += '\n'

	eprint(res)


for line in intmat:
	px, py = None, None
	for x, y in [line[i:i + 2] for i in range(0, len(line), 2)]:
		if px is None:
			px, py = x, y
			continue

		if y == py:
			for i in autorange(x, px):
				rock.add((i, y))
		elif x == px:
			for i in autorange(y, py):
				rock.add((x, i))
		else:
			assert False

		px, py = x, y

floory = max(map(itemgetter(1), rock)) + 2

def occ(p):
	return p in rock or p in sand or p[1] == floory

def pour(part2=False):
	x = 500
	y = 0
	p = x, y

	if part2 and occ(p):
		return True

	while 1:
		x, y = p
		if not occ((x, y + 1)):
			p = (x, y + 1)
			continue

		l = (x - 1, y + 1)
		r = (x + 1, y + 1)

		if not occ(l):
			p = l
			continue

		if not occ(r):
			p = r
			continue

		break

	if not part2 and p[1] + 1 == floory:
		return True

	sand.add(p)
	return False

while not pour():
	ans += 1
	# dump()

advent.print_answer(1, ans)


while not pour(True):
	ans += 1
	# dump()

advent.print_answer(2, ans)
