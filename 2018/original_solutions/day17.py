#!/usr/bin/env python3

from utils import advent
import re

advent.setup(2018, 17)
fin = advent.get_input()
# print(*fin)

##################################################

rexp  = re.compile(r'-?\d+')
minx, miny = 9999, 9999
maxx, maxy = -9999, -9999

horizontal = []
vertical = []

for l in fin:
	a, b, c = map(int, rexp.findall(l))

	if l.startswith('x'):
		minx = min(minx, a)
		maxx = max(maxx, a)
		miny = min(miny, b)
		maxy = max(maxy, c)

		vertical.append([a, b, c])
	else:
		miny = min(miny, a)
		maxy = max(maxy, a)
		minx = min(minx, b)
		maxx = max(maxx, c)

		horizontal.append([a, b, c])

# print('Horizontal:')
# for h in horizontal:
# 	print(h)

# print('Vertical:')
# for v in vertical:
# 	print(v)

for i in range(len(horizontal)):
	horizontal[i][0] -= miny
	horizontal[i][1] -= minx
	horizontal[i][2] -= minx

for i in range(len(vertical)):
	vertical[i][0] -= minx
	vertical[i][1] -= miny
	vertical[i][2] -= miny

# print('Horizontal:')
# for h in horizontal:
# 	print(h)

# print('Vertical:')
# for v in vertical:
# 	print(v)

SAND = 0
WATER = 1
MOVING_WATER = 2
CLAY = 3

gridw = maxx-minx+1
gridh = maxy-miny+1

# print('x', minx, maxx)
# print('y', miny, maxy)
# print('w', gridw)
# print('h', gridh)

grid = []

for _ in range(gridh):
	grid.append([SAND] * gridw)

for y, x1, x2 in horizontal:
	for x in range(x1, x2+1):
		grid[y][x] = CLAY

for x, y1, y2 in vertical:
	for y in range(y1, y2+1):
		grid[y][x] = CLAY

# Pad borders
gridh += 1
gridw += 2

for i in range(len(grid)):
	grid[i] = [SAND] + grid[i] + [SAND]

grid = [[SAND] * gridw] + grid


# with open('viz_initial.txt', 'w') as f:
# 	for line in grid:
# 		f.write(''.join(map('.~|#'.__getitem__, line)) + '\n')


def spread(sx, sy):
	grid[sy][sx] = WATER
	new_sources  = set()

	if grid[sy+1][sx] == WATER:
		should_spread = False
		prev = WATER

		for cell in grid[sy+1][sx+1:]:
			if prev == WATER and cell == CLAY:
				should_spread = True
				break
			elif prev != WATER:
				break
			prev = cell

		if not should_spread:
			return

		should_spread = False
		prev = WATER

		for cell in grid[sy+1][sx-1::-1]:
			if prev == WATER and cell == CLAY:
				should_spread = True
				break
			elif prev != WATER:
				break
			prev = cell

		if not should_spread:
			return

	x = sx + 1
	while x < gridw and grid[sy][x] == SAND and grid[sy+1][x] != SAND:
		grid[sy][x] = WATER
		x += 1

	if x < gridw and grid[sy+1][x] == SAND:
		new_sources.add((x, sy))

	x = sx - 1
	while x >= 0 and grid[sy][x] == SAND and grid[sy+1][x] != SAND:
		grid[sy][x] = WATER
		x -= 1

	if x >= 0 and grid[sy+1][x] == SAND:
		new_sources.add((x, sy))

	return new_sources

def fill(sx, sy, recdepth=0):
	# if recdepth == 3:
	# 	return

	y = sy
	while y < gridh and grid[y][sx] == SAND:
		y += 1

	if y >= gridh:
		for y in range(sy, gridh):
			grid[y][sx] = WATER
		return

	y -= 1


	for yy in range(y, sy-1, -1):
		new_sources = spread(sx, yy)

		if new_sources:
			for s in new_sources:
				fill(*s, recdepth+1)


fill(500 - minx + 1, 0)


# try:
# 	fill(500 - minx + 1, 0)
# except IndexError:
# 	print('IndexError!!!')
# 	pass


# with open('viz_filled.txt', 'w') as f:
# 	for line in grid:
# 		f.write(''.join(map(' ~|#'.__getitem__, line)) + '\n')


filled = 0
for row in grid[1:]:
	for cell in row:
		if cell == WATER:
			filled += 1

advent.submit_answer(1, filled)


# Assuming that a situation like this one will never happen:

#      #
# #~~~X#
# #~~#X#
# ####X#
#     X#

retained = filled

for row in grid:
	prev = SAND

	for x, cell in enumerate(row):
		if cell == WATER and prev in (SAND, MOVING_WATER):
			retained -= 1
			row[x] = MOVING_WATER

		prev = row[x]

	prev = SAND
	for x, cell in enumerate(row[::-1]):
		if cell == WATER and prev in (SAND, MOVING_WATER):
			retained -= 1
			row[gridw - 1 - x] = MOVING_WATER

		prev = row[gridw - 1 - x]


# with open('viz_filled.txt', 'w') as f:
# 	for line in grid:
# 		f.write(''.join(map(' ~|#'.__getitem__, line)) + '\n')

filled = 0
for row in grid[1:]:
	for cell in row:
		if cell == WATER:
			filled += 1

# 25447 too low
advent.submit_answer(2, filled)
