#!/usr/bin/env python3

from utils.all import *

# https://stackoverflow.com/a/20677983/3889449
def line_intersection(line1, line2):
	xdiff = (line1[0][0] - line1[1][0], line2[0][0] - line2[1][0])
	ydiff = (line1[0][1] - line1[1][1], line2[0][1] - line2[1][1])

	def det(a, b):
		return a[0] * b[1] - a[1] * b[0]

	div = det(xdiff, ydiff)
	if div == 0:
		return None, None

	d = (det(*line1), det(*line2))
	x = det(d, xdiff) / div
	y = det(d, ydiff) / div
	return x, y


advent.setup(2023, 24)
fin = advent.get_input()

lines = read_lines(fin)
stuff = []

for line in lines:
	x, y, z, vx, vy, vz = extract_ints(line)
	stuff.append((Vec(x,y,z), Vec(vx, vy, vz)))

tot = 0
for a, b in combinations(stuff, 2):
	a, va = a
	b, vb = b

	x, y = line_intersection((a, a + va), (b, b + vb))
	# print(a, va, '|', b, vb, '->', x, y)

	if x is None:
		continue

	# If it's in the future the signs of the velocity and the delta must be the same
	dx = x - a.x
	dy = y - a.y
	if (dx > 0) == (va.x > 0) and (dy > 0) == (va.y > 0):
		# print('future')
		...
	else:
		continue

	# If it's in the future the signs of the velocity and the delta must be the same
	dx = x - b.x
	dy = y - b.y
	if (dx > 0) == (vb.x > 0) and (dy > 0) == (vb.y > 0):
		# print('future')
		...
	else:
		continue

	if 200000000000000 <= x <= 400000000000000 and 200000000000000 <= y <= 400000000000000:
		tot += 1

advent.print_answer(1, tot)


import z3

# BitVec is way faster than Int
I = lambda name: z3.BitVec(name, 64)

x, y, z = I('x'), I('y'), I('z')
vx, vy, vz = I('vx'), I('vy'), I('vz')

s = z3.Solver()

for i, a in enumerate(stuff):
	(ax, ay, az), (vax, vay, vaz) = a

	t = I(f't_{i}')
	s.add(t >= 0)
	s.add(x + vx * t == ax + vax * t)
	s.add(y + vy * t == ay + vay * t)
	s.add(z + vz * t == az + vaz * t)

assert s.check() == z3.sat

m = s.model()
x, y, z = m.eval(x), m.eval(y), m.eval(z)
x, y, z = x.as_long(), y.as_long(), z.as_long()

ans2 = x + y + z
advent.print_answer(2, ans2)
