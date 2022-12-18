#!/usr/bin/env python3

from collections import deque
from itertools import product
from operator import itemgetter

from utils import advent

def neighbors(x, y, z):
	yield (x + 1, y    , z    )
	yield (x - 1, y    , z    )
	yield (x    , y + 1, z    )
	yield (x    , y - 1, z    )
	yield (x    , y    , z + 1)
	yield (x    , y    , z - 1)

def escape(cubes, src, rangex, rangey, rangez):
	seen = set()
	queue = deque([src])
	faces_touched = 0

	while queue:
		p = queue.pop()
		if p in seen:
			continue

		seen.add(p)
		x, y, z, = p

		if x not in rangex or y not in rangey or z not in rangez:
			return 0, seen

		for n in neighbors(x, y, z):
			if n in cubes:
				faces_touched += 1
			elif n not in seen:
				queue.append(n)

	return faces_touched, seen


advent.setup(2022, 18)

cubes = {}
with advent.get_input() as fin:
	for line in fin:
		cubes[tuple(map(int, line.split(',')))] = 6

for c in cubes:
	cubes[c] -= sum(n in cubes for n in neighbors(*c))

surface = sum(cubes.values())
advent.print_answer(1, surface)


allseen = set()
rangex  = range(min(map(itemgetter(0), cubes)), max(map(itemgetter(0), cubes)) + 1)
rangey  = range(min(map(itemgetter(1), cubes)), max(map(itemgetter(1), cubes)) + 1)
rangez  = range(min(map(itemgetter(2), cubes)), max(map(itemgetter(2), cubes)) + 1)

for c in product(rangex, rangey, rangez):
	if c not in cubes and c not in allseen:
		touched, seen = escape(cubes, c, rangex, rangey, rangez)
		allseen |= seen

		if touched:
			surface -= touched

advent.print_answer(2, surface)
