#!/usr/bin/env python3

import utils
import re

def should_spread(sx, sy):
	if grid[sy+1][sx] != WATER:
		return True

	prev = WATER

	for cell in grid[sy+1][sx+1:]:
		if prev != WATER: return False
		if cell == CLAY : break
		prev = cell

	for cell in grid[sy+1][sx-1::-1]:
		if prev != WATER: return False
		if cell == CLAY : break
		prev = cell

	return True

def spread(sx, sy):
	grid[sy][sx] = WATER
	new_sources  = set()
	water_count  = 1

	if should_spread(sx, sy):
		for x in range(sx + 1, gridw):
			if grid[sy][x] != SAND or grid[sy+1][x] == SAND:
				break

			grid[sy][x] = WATER
			water_count += 1

		if grid[sy+1][x] == SAND:
			new_sources.add((x, sy))

		for x in range(sx - 1, -1, -1):
			if grid[sy][x] != SAND or grid[sy+1][x] == SAND:
				break

			grid[sy][x] = WATER
			water_count += 1

		if grid[sy+1][x] == SAND:
			new_sources.add((x, sy))

	return new_sources, water_count

def fill(sx, sy):
	total_water = 0

	reached_bottom = True
	for bottom_y in range(sy, gridh):
		if grid[bottom_y][sx] != SAND:
			reached_bottom = False
			break

	if reached_bottom:
		for y in range(sy, gridh):
			grid[y][sx] = WATER
		return total_water + gridh - sy

	bottom_y -= 1

	for y in range(bottom_y, sy - 1, -1):
		new_sources, water_count = spread(sx, y)
		total_water += water_count

		for s in new_sources:
			total_water += fill(*s)

	return total_water


SAND, WATER, MOVING_WATER, CLAY = range(4)

utils.setup(2018, 17, dry_run=True)
fin = utils.get_input()

numexp     = re.compile(r'-?\d+')
minx, miny = +9999, +9999
maxx, maxy = -9999, -9999
horizontal = []
vertical   = []

for line in fin:
	a, b, c = map(int, numexp.findall(line))

	if line[0] == 'x':
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

for h in horizontal:
	h[0] -= miny
	h[1] -= minx
	h[2] -= minx

for v in vertical:
	v[0] -= minx
	v[1] -= miny
	v[2] -= miny

gridw = maxx - minx + 1
gridh = maxy - miny + 1
grid  = [[SAND for _ in range(gridw)] for _ in range(gridh)]

for y, x1, x2 in horizontal:
	for x in range(x1, x2 + 1):
		grid[y][x] = CLAY

for x, y1, y2 in vertical:
	for y in range(y1, y2 + 1):
		grid[y][x] = CLAY

gridh += 1
gridw += 2

for i in range(len(grid)):
	grid[i] = [SAND] + grid[i] + [SAND] # pad left and right
grid = [[SAND] * gridw] + grid          # pad top


filled = fill(500 - minx + 1, 0) - 1
# assert filled == 31013

utils.submit_answer(1, filled)

# The following code is assuming that a situation like this
# one does not happen (in such case the water marked with X
# would incorrectly be considered "still").

# .|...#      .|...#
# #||||#      #XXXX#
# #~~#|# ---> #~~#X#
# ####|#      ####X#
# ....|#      ....|#

still = filled

for row in grid[1:]:
	prev = SAND
	for x, cell in enumerate(row):
		if cell == WATER and prev in (SAND, MOVING_WATER):
			row[x] = MOVING_WATER
			still -= 1
		prev = row[x]

	prev = SAND
	for x, cell in enumerate(row[::-1]):
		if cell == WATER and prev in (SAND, MOVING_WATER):
			row[gridw-x-1] = MOVING_WATER
			still -= 1
		prev = row[gridw-x-1]

# assert still == 25448

utils.submit_answer(2, still)
