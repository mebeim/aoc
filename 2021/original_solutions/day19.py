#!/usr/bin/env python3

from utils.all import *

DEBUG = 'debug' in map(str.lower, sys.argv)
if not DEBUG:
	fin = advent.get_input()

def cos(x):
	if x == 90:
		return 0
	if x == 180:
		return -1
	if x == 270:
		return 0
	assert x == 0
	return 1

def sin(x):
	if x == 90:
		return 1
	if x == 180:
		return 0
	if x == 270:
		return -1
	assert x == 0
	return 0

def rotate3d_z(x, y, z, theta):
	c, s = cos(theta), sin(theta)
	return (x*c - y*s, x*s+y*c, z)

def rotate3d_x(x, y, z, theta):
	c, s = cos(theta), sin(theta)
	return (x, y*c - z*s, y*s + z*c)

def rotate3d_y(x, y, z, theta):
	c, s = cos(theta), sin(theta)
	return (x*c + z*s, y, -x*s + z*c)

def apply(rx, ry, rz):
	def f(x, y, z):
		nonlocal rx, ry, rz
		x, y, z = rotate3d_x(x, y, z, rx)
		x, y, z = rotate3d_y(x, y, z, ry)
		return rotate3d_z(x, y, z, rz)
	return f

facings = [
	apply(  0,   0,   0),
	apply( 90,   0,   0),
	apply(180,   0,   0),
	apply(270,   0,   0),
	apply(  0,  90,   0),
	apply( 90,  90,   0),
	apply(180,  90,   0),
	apply(270,  90,   0),
	apply(  0, 180,   0),
	apply( 90, 180,   0),
	apply(180, 180,   0),
	apply(270, 180,   0),
	apply(  0, 270,   0),
	apply( 90, 270,   0),
	apply(180, 270,   0),
	apply(270, 270,   0),
	apply(  0,   0,  90),
	apply( 90,   0,  90),
	apply(180,   0,  90),
	apply(270,   0,  90),
	apply(  0,   0, 270),
	apply( 90,   0, 270),
	apply(180,   0, 270),
	apply(270,   0, 270),
]

assert len(facings) == 24

p = (1, 2, 3)
s = set()
for f in facings:
	s.add(f(*p))

assert len(s) == 24

if DEBUG:
	fin = io.StringIO('''\
--- scanner 0 ---
0,2,0
4,1,0
3,3,0

--- scanner 1 ---
-1,-1,0
-5,0,0
-2,1,0
0,1,0
1,1,0
2,1,0

--- scanner 2 --- basis with inverted x and y axis
0,2,1
1,2,1
2,2,1
''')


lines = get_lines(fin)
timer_start()

ans = 0
scanners = []

for line in lines:
	if not line:
		continue
	if line.startswith('---'):
		scanners.append([])
		continue

	scanners[-1].append(tuple(map(int, line.split(','))))

scanners = list(map(set, scanners))


vbase = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
vx, vy, vz = vbase
bases = []

for f in facings:
	bases.append((f(*vx), f(*vy), f(*vz)))

# dump_iterable(sorted(bases))
assert len(set(bases)) == 24

# transform to coords from given basis to basis ((1, 0, 0), (0, 1, 0), (0, 0, 1))
def basis_transform(v, basis):
	a,b,c = basis[0]
	d,e,f = basis[1]
	g,h,i = basis[2]
	x,y,z = v
	return (a*x+b*y+c*z, d*x+e*y+f*z, g*x+h*y+i*z)

def diff(a, b):
	ax, ay, az = a
	bx, by, bz = b
	return (ax - bx, ay - by, az - bz)

def add(a, b):
	ax, ay, az = a
	bx, by, bz = b
	return (ax + bx, ay + by, az + bz)

def manhattan(a, b):
	ax, ay, az = a
	bx, by, bz = b
	return abs(ax - bx) + abs(ay - by) + abs(az - bz)

print('there are', len(scanners), 'scanners')


MATCH_THRESHOLD = 12

def common_points(s1, s2, i1, i2):
	# assume s1 is in "normal" base ((1, 0, 0), (0, 1, 0), (0, 0, 1))
	# make s2 face any possible way (any base), then convert its points to normal base
	#
	# then for each pair of points p1, p2 (p2 in normal base):
	#    if p1 and p2 identify the same beacon for s1 and s2, then p1 - p2 is the
	#    distance vector from s1 to s2
	#    this means that if we get this distance, and translate all points of s2 by
	#    this distance, we can check if at least 12 should line up with those of s1

	for basis in bases:
		new_s2 = tuple(basis_transform(vec, basis) for vec in s2)

		for p1, p2 in product(s1, new_s2):
			dist = diff(p1, p2)
			translated_s2 = set(add(p, dist) for p in new_s2)

			if len(s1 & translated_s2) >= MATCH_THRESHOLD:
				eprint('scanners', i1, 'and', i2, 'match: distance', dist, 'basis', basis)
				return translated_s2, dist

	return None, None

matched = {0: scanners[0]}
distances = [(0,0,0)]
done = set()

while True:
	for i in range(len(scanners)):
		if i in done or i not in matched:
			continue

		for j in range(len(scanners)):
			if j in matched or i == j:
				continue

			common, dist = common_points(matched[i], scanners[j], i, j)

			if common is not None:
				matched[j] = common
				distances.append(dist)

		done.add(i)

	if len(done) == len(scanners):
		break

all_points = reduce(set.union, matched.values())
ans = len(all_points)

# 799 bad
advent.print_answer(1, ans)

# dump_dict(distances)
best = max(starmap(manhattan, combinations(distances, 2)))

# 12238 nope
advent.print_answer(2, best)

# Bif OOF!
# cpython Timer ./day19.py: 20.218s wall, 20.217s CPU
# pypy    Timer ./day19.py: 7.776s wall, 7.776s CPU
