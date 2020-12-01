#!/usr/bin/env python3

from utils.all import *
from fractions import Fraction

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

charmat = get_char_matrix(fin)

def frac(x1, y1, x2, y2):
	if x1 == x2:
		return 'inf', -1 if y1 > y2 else 1

	f = Fraction(y2 - y1, x2 - x1)

	if f == 0:
		return f, -1 if x1 > x2 else 1
	return f, -1 if y1 > y2 else 1

def dist2(x1, y1, x2, y2):
	return (x2-x1)**2 + (y2-y1)**2

ast = set()

for y in range(len(charmat)):
	for x in range(len(charmat[y])):
		if charmat[y][x] != '.':
			ast.add((x, y))

in_sight = defaultdict(int)

# aligned = defaultdict(set)

set_in_sight = defaultdict(dict)

# print('total', len(ast))

for i, a in enumerate(ast):
	# print(i)
	los = set()

	for b in ast:
		if a == b:
			continue

		m = frac(*a, *b)

		# aligned[m].add(b)

		d = dist2(*a, *b)

		if m in set_in_sight[a]:
			prevd = dist2(*a, *set_in_sight[a][m])

			if prevd > d:
				set_in_sight[a][m] = b
		else:
			set_in_sight[a][m] = b

		if m not in los:
			in_sight[a] += 1
			los.add(m)

best = max(in_sight, key=lambda k: in_sight[k])
# print(best, in_sight[best])

# 712 wrong
# 285 too low
# 286 too low
advent.submit_answer(1, in_sight[best])

from math import atan2, pi
import cmath

def key_angle(src):
	sx, sy = src

	def k(a):
		ax, ay = a
		x = ax-sx
		y = ay-sy
		rad = atan2(y, x)
		deg = (rad if rad > 0 else (2*pi + rad)) * 360 / (2*pi)

		if deg == 360:
			deg = 0

		deg += 90.0
		if deg > 360:
			deg = deg - 360

		if deg == 360:
			deg = 0

		return deg # hey, it if works it works...

	return k

keyfunc = key_angle(best)
target = 200

while True:
	in_sight = defaultdict(int)
	set_in_sight = defaultdict(dict)

	for i, a in enumerate(ast):
		# print(i)
		los = set()

		for b in ast:
			if a == b:
				continue

			m = frac(*a, *b)

			# aligned[m].add(b)

			d = dist2(*a, *b)

			if m in set_in_sight[a]:
				prevd = dist2(*a, *set_in_sight[a][m])

				if prevd > d:
					set_in_sight[a][m] = b
			else:
				set_in_sight[a][m] = b

			if m not in los:
				in_sight[a] += 1
				los.add(m)

	to_kill = len(set_in_sight[best])
	assert to_kill != 0, 'wtf'


	if to_kill < target:
		target -= to_kill
	else:
		ordered = sorted(set_in_sight[best].values(), key=keyfunc)
		# for o in ordered:
		# 	print(keyfunc(o), o)
		chosen = ordered[target - 1]
		break

# print('>', chosen)

advent.submit_answer(2, chosen[0] * 100 + chosen[1])
