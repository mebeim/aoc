#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 22)

DEBUG = 'debug' in map(str.lower, sys.argv)
if not DEBUG:
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
"on x=10..12,y=10..12,z=10..12",
"on x=11..13,y=11..13,z=11..13",
"off x=9..11,y=9..11,z=9..11",
"on x=10..10,y=10..10,z=10..10",
''')

# eprint(*fin, sep='', end='----- end of input -----\n\n'); fin.seek(0, 0)
timer_start()

try: ints = get_ints(fin, True); fin.seek(0, 0)
except: pass
try: lines = get_lines(fin); fin.seek(0, 0)
except: pass
try: mat = get_char_matrix(fin, rstrip=False, lstrip=False); fin.seek(0, 0)
except: pass

cub = set()
parsed = []

# print(len(lines), 'lines')

for line in lines:
	x1, x2, y1, y2, z1, z2 = map(int, re.findall(r'-?\d+', line))
	parsed.append(('on' in line, x1, y1, z1, x2 + 1, y2 + 1, z2 + 1))

	if line.startswith('on'):
		for x in range(max(x1, -50), min(x2, 50) + 1):
			for y in range(max(y1, -50), min(y2, 50) + 1):
				for z in range(max(z1, -50), min(z2, 50) + 1):
					# print('+', (x, y, z))
					cub.add((x, y, z))
	else:
		for x in range(max(x1, -50), min(x2, 50) + 1):
			for y in range(max(y1, -50), min(y2, 50) + 1):
				for z in range(max(z1, -50), min(z2, 50) + 1):

					try:
						cub.remove((x, y, z))
						# print('-', (x, y, z))
					except KeyError:
						continue

ans = 0
for x in range(-50, 50 + 1):
	for y in range(-50, 50 + 1):
		for z in range(-50, 50 + 1):
			ans += (x, y, z) in cub

# 8402 nope
advent.print_answer(1, ans)
# wait('Submit? ')
# advent.submit_answer(1, ans)

class Cuboid:
	__slots__ = ('x1', 'x2', 'y1', 'y2', 'z1', 'z2')
	def __init__(self, x1, y1, z1, x2, y2, z2):
		assert x1 <= x2 and y1 <= y2 and z1 <= z2, f'{x1, y1, z1, x2, y2, z2}'
		self.x1 = x1
		self.x2 = x2
		self.y1 = y1
		self.y2 = y2
		self.z1 = z1
		self.z2 = z2

	def __contains__(self, other):
		return self.x1 <= other.x1 and self.x2 >= other.x2 \
			and self.y1 <= other.y1 and self.y2 >= other.y2 \
			and self.z1 <= other.z1 and self.z2 >= other.z2 \

	def __and__(self, other): # other overlaps with self?
		return self.x1 <= other.x2 and self.x2 >= other.x1 \
			and self.y1 <= other.y2 and self.y2 >= other.y1 \
			and self.z1 <= other.z2 and self.z2 >= other.z1

	def __sub__(self, other):
		if self in other:
			return

		if not (self & other):
			yield self
			return

		x1, x2, y1, y2, z1, z2 = self.x1, self.x2, self.y1, self.y2, self.z1, self.z2
		a1, a2, b1, b2, c1, c2 = other.x1, other.x2, other.y1, other.y2, other.z1, other.z2

		xs = [x1]
		if x1 < a1 < x2: xs.append(a1)
		if x1 < a2 < x2: xs.append(a2)
		xs.append(x2)

		ys = [y1]
		if y1 < b1 < y2: ys.append(b1)
		if y1 < b2 < y2: ys.append(b2)
		ys.append(y2)

		zs = [z1]
		if z1 < c1 < z2: zs.append(c1)
		if z1 < c2 < z2: zs.append(c2)
		zs.append(z2)

		for xfrom, xto in zip(xs, xs[1:]):
			for yfrom, yto in zip(ys, ys[1:]):
				for zfrom, zto in zip(zs, zs[1:]):
					cub = Cuboid(xfrom, yfrom, zfrom, xto, yto, zto)

					if cub in other or cub.volume() <= 0:
						continue

					yield cub

	def volume(self):
		v = (self.x2 - self.x1) * (self.y2 - self.y1) * (self.z2 - self.z1)
		assert v >= 0
		return v

	def __repr__(self):
		return f'<{self.volume()} ~ {self.x1} {self.y1} {self.z1} ~ {self.x2} {self.y2} {self.z2}>'

# a, b = Cuboid(0, 0, 0, 3, 3, 3), Cuboid(1, 1, 1, 2, 2, 2)
# print('a in b', a in b)
# print('b in a', b in a)
# print(a)
# print(b)
# eprint('---')

# newv = 0
# for diff in (a - b):
# 	print(diff)
# 	newv += diff.volume()

# print('a', a.volume())
# print('b', b.volume())
# print('a - b', a.volume() - b.volume())
# print('newv', newv)
# assert newv == a.volume() - b.volume()


cuboids = []

for ison, *coords in parsed:
	cub = Cuboid(*coords)
	# eprint(ison, cub)

	new_cuboids = []

	for other in cuboids:
		new_cuboids.extend(other - cub)

	cuboids = new_cuboids

	if ison:
		cuboids.append(cub)

	# eprint(len(cuboids), cuboids)

ans = sum(c.volume() for c in cuboids)

advent.print_answer(2, ans)
# wait('Submit? ')
# advent.submit_answer(2, ans)
