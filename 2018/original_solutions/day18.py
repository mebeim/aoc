#!/usr/bin/env python3

from utils import advent

import sys
import copy

advent.setup(2018, 18)
fin = advent.get_input()
# print(*fin)

##################################################

strings = list(map(str.strip, fin))
grid = []

EMPTY, TREE, LUMB = range(3)

mapped = {
	'.': EMPTY,
	'|': TREE,
	'#': LUMB
}

for s in strings:
	grid.append([])
	for c in s:
		grid[-1].append(mapped[c])

gridw = len(grid)
gridh = len(grid[0])

def dump(grid):
	for line in grid:
 		sys.stdout.write(''.join(map('.|#'.__getitem__, line)) + '\n')

def adj(curgrid, x, y):
	for dx in range(-1, 2):
		for dy in range(-1, 2):
			nx, ny = x+dx, y+dy

			if (dx, dy) != (0, 0) and 0 <= nx < gridw and 0 <= ny < gridh:
				# print(dx, dy, curgrid[nx][ny])
				yield curgrid[nx][ny]

# for a in adj(grid, 2, 8):
# 	continue

# sys.exit()

def transform(curgrid, x, y):
	nempty = 0
	ntrees = 0
	nlumb = 0

	for cell in adj(curgrid, x, y):
		if cell == EMPTY:
			nempty += 1
		elif cell == TREE:
			ntrees += 1
		elif cell == LUMB:
			nlumb += 1

	# print(x, y, ':', nempty, ntrees, nlumb)

	if curgrid[x][y] == EMPTY:
		if ntrees >= 3:
			return TREE
		return EMPTY
	elif curgrid[x][y] == TREE:
		if nlumb >= 3:
			return LUMB
		return TREE
	elif curgrid[x][y] == LUMB:
		if not (nlumb >= 1 and ntrees >= 1):
			return EMPTY
		return LUMB

def get_ans(curgrid):
	ntrees = 0
	nlumb = 0

	for x in range(gridw):
		for y in range(gridh):
			if curgrid[x][y] == TREE:
				ntrees += 1
			elif grid[x][y] == LUMB:
				nlumb += 1

	return ntrees * nlumb

states = set()


for i in range(10):
	curstate = get_ans(grid)
	states.add(curstate)

	newgrid = copy.deepcopy(grid)

	for x in range(gridw):
		for y in range(gridh):
			newgrid[x][y] = transform(grid, x, y)

	grid = newgrid

res = get_ans(grid)
advent.submit_answer(1, res)

# dump(grid)

for i in range(10, 1000000000):
	curstate = get_ans(grid)

	if curstate not in states:
		states.add(curstate)
		print(i, ':', curstate)
	else:
		print('---->', i, ':', curstate)


	newgrid = copy.deepcopy(grid)

	for x in range(gridw):
		for y in range(gridh):
			newgrid[x][y] = transform(grid, x, y)

	# sys.exit()

	# print()
	# dump(newgrid)

	grid = newgrid

	if i > 3909:
		break

period = {
	3882: 199470,
	3883: 202048,
	3884: 205296,
	3885: 210420,
	3886: 212758,
	3887: 217638,
	3888: 222264,
	3889: 226548,
	3890: 229856,
	3891: 233774,
	3892: 235440,
	3893: 235372,
	3894: 235011,
	3895: 235790,
	3896: 232683,
	3897: 230505,
	3898: 227069,
	3899: 225060,
	3900: 219198,
	3901: 216948,
	3902: 210951,
	3903: 206562,
	3904: 201705,
	3905: 199841,
	3906: 197540,
	3907: 197276,
	3908: 195600,
	3909: 198112
}

res = period[3882 + (1000000000-3882) % len(period)]

advent.submit_answer(2, res)
