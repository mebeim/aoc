#!/usr/bin/env python3

from utils.all import *

def succ(x, y, z):
	yield (x+1, y  , z)
	yield (x  , y+1, z)
	yield (x  , y  , z+1)
	yield (x-1, y  , z)
	yield (x  , y-1, z)
	yield (x  , y  , z-1)

def escape(cubeset, src, minx, miny, minz, maxx, maxy, maxz):
	q = deque([src])
	seen = set()
	faces_touched = 0

	while q:
		p = q.pop()
		if p in seen:
			continue

		# eprint(p)

		seen.add(p)
		x, y, z, = p

		if x > maxx or x < minx or y > maxy or y < miny or z > maxz or z < minz:
			# eprint('ESCAPE')
			return 0, None

		for p2 in succ(x, y, z):
			if p2 in cubeset:
				faces_touched += 1
			elif p2 not in seen:
				q.append(p2)

	return faces_touched, seen

def conn(a, b):
	if a - b in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
		return True
	if b - a in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
		return True
	return False


advent.setup(2022, 18)
fin = advent.get_input()
intmat = read_int_matrix(fin)
timer_start()

ans = 0
cubes = []
for line in intmat:
	cubes.append(Vec(*line))

isconn = {tuple(x): 6 for x in cubes}

for a, b in combinations(cubes, 2):
	if conn(a, b):
		isconn[tuple(a)] -= 1
		isconn[tuple(b)] -= 1

for c, v in isconn.items():
	ans += v

advent.print_answer(1, ans)


minx, maxx = min(map(itemgetter(0), cubes)), max(map(itemgetter(0), cubes))
miny, maxy = min(map(itemgetter(1), cubes)), max(map(itemgetter(1), cubes))
minz, maxz = min(map(itemgetter(2), cubes)), max(map(itemgetter(2), cubes))

minx-=1
miny-=1
minz-=1
maxx+=1
maxy+=1
maxz+=1

allseen = set()
cubeset = set(map(tuple, cubes))

for x in range(minx, maxx + 1):
	for y in range(miny, maxy + 1):
		for z in range(minz, maxz + 1):
			c = (x, y, z)

			if c not in cubeset and c not in allseen:
				# eprint('checking', c)
				touched, seen = escape(cubeset, c, minx, miny, minz, maxx, maxy, maxz)

				if touched:
					ans -= touched
					allseen |= seen

advent.print_answer(2, ans)
