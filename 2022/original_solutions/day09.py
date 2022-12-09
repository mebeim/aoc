#!/usr/bin/env python3

from utils.all import *

advent.setup(2022, 9)

DEBUG = 'debug' in map(str.lower, sys.argv)
if not DEBUG:
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
R 5
U 8
L 8
D 3
R 17
D 10
L 25
U 20
''')

lines = get_lines(fin)

ans = 0
hx, hy = 0, 0
tx, ty = 0, 0
hpx, hpy = None, None

seen = {(tx, ty)}

def show(hx, hy, o):
	m = []
	for y in range(-5,10):
		m.append([])
		for x in range(-10,20):
			for i, (ox, oy) in enumerate(o, 1):
				if (x, y) == (ox, oy):
					m[-1].append(str(i))
					break
			else:
				if (x, y) == (hx, hy):
					m[-1].append('H')
				else:
					m[-1].append('.')
	dump_char_matrix(m[::-1])

for l in lines:
	d, n = l.split()
	n = int(n)

	for i in range(n):
		if d == 'U':
			hy += 1
		elif d == 'D':
			hy -= 1
		elif d == 'L':
			hx -= 1
		elif d == 'R':
			hx += 1

		dist = abs(hx - tx) + abs(hy - ty)
		if ((hx == tx or hy == ty) and dist > 1) or dist > 2:
			tx, ty = hpx, hpy
			seen.add((tx, ty))

		hpx, hpy = hx, hy

ans = len(seen)
advent.print_answer(1, ans)

r = [[0, 0] for _ in range(10)]
seen = set()

for l in lines:
	d, n = l.split()
	n = int(n)
	# eprint('='*80, l)

	for i in range(n):
		# show(*r[0], r[1:])
		# eprint('---')

		if d == 'U':
			r[0][1] += 1
		elif d == 'D':
			r[0][1] -= 1
		elif d == 'L':
			r[0][0] -= 1
		elif d == 'R':
			r[0][0] += 1

		for j in range(1, 10):
			hx, hy = r[j - 1][:]
			tx, ty = r[j][:]
			dx = hx - tx
			dy = hy - ty

			if dx**2 + dy**2 >= 4:
				if dx:
					tx += 1 if dx > 0 else -1
				if dy:
					ty += 1 if dy > 0 else -1
				r[j] = [tx, ty]

		seen.add(tuple(r[9]))

ans = len(seen)

# 4566 wrong
advent.print_answer(2, ans)
