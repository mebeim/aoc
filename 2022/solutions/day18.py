#!/usr/bin/env python3

import sys
from collections import deque
from itertools import product
from operator import itemgetter

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


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

cubes = {}
for line in fin:
	cubes[tuple(map(int, line.split(',')))] = 6

for c in cubes:
	cubes[c] -= sum(n in cubes for n in neighbors(*c))

surface = sum(cubes.values())
print('Part 1:', surface)


allseen = set()
rangex  = range(min(map(itemgetter(0), cubes)), max(map(itemgetter(0), cubes)) + 1)
rangey  = range(min(map(itemgetter(1), cubes)), max(map(itemgetter(1), cubes)) + 1)
rangez  = range(min(map(itemgetter(2), cubes)), max(map(itemgetter(2), cubes)) + 1)

for c in product(rangex, rangey, rangez):
	if c not in cubes and c not in allseen:
		touched, seen = escape(cubes, c, rangex, rangey, rangez)
		surface -= touched
		allseen |= seen

print('Part 2:', surface)
