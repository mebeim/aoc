#!/usr/bin/env python3
#
# Solve part 1 and part 2 of the problem and crate two PNG visualizations of the
# state of the final cave: one for part 1 and one for part 2.
#

import sys
from pathlib import Path
from operator import itemgetter
from PIL import Image, ImageDraw

def autorange(a, b):
	return range(a, b + 1) if a <= b else range(a, b - 1, -1)

def range2d(a, b):
	ax, ay = a
	bx, by = b

	if ax == bx:
		for y in autorange(ay, by):
			yield ax, y
	else:
		for x in autorange(ax, bx):
			yield x, ay

def pour_sand(cave, maxy, floor=False, x=500, y=0):
	if y == maxy and not floor:
		return True

	if y <= maxy or not floor:
		newy = y + 1

		for newx in (x, x - 1, x + 1):
			if (newx, newy) not in cave and pour_sand(cave, maxy, floor, newx, newy):
				return True

	cave.add((x, y))
	return False

def create_image(cave, rocks, fname):
	miny, maxy = 0, max(map(itemgetter(1), cave))
	minx, maxx = min(map(itemgetter(0), cave)) - 1, max(map(itemgetter(0), cave))

	scale = 8
	translate_y = 1

	w, h = maxx + 2 - minx, maxy + 2 - miny + translate_y
	im = Image.new('RGB', (w * scale, h * scale))
	dr = ImageDraw.Draw(im)

	for y in range(miny - translate_y, maxy + 3):
		for x in range(minx, maxx + 2):
			if (x, y) in rocks:
				color = '#59534f'
			elif (x, y) in cave:
				color = (234, 212, 157)
			else:
				color = (8, 6, 20)

			yy = y - miny + translate_y
			xx = x - minx
			dr.rectangle([(xx * scale, yy * scale), ((xx + 1) * scale - 1, (yy + 1) * scale - 1)], fill=color)

	x, y = 500 - minx, translate_y
	dr.rectangle([(x * scale, y * scale), ((x + 1) * scale - 1, (y + 1) * scale - 1)], fill=(255, 0, 0))

	im.save(fname)


if len(sys.argv) != 2:
	sys.exit(f'Usage {sys.argv[0]} path/to/input.txt')

fin = Path(sys.argv[1])

if not fin.exists():
	sys.exit(f'"{fin}" not found')

if not fin.is_file():
	sys.exit(f'"{fin}" is not a file')


cave = set()

with fin.open() as f:
	for line in f:
		points = (tuple(map(int, p.split(','))) for p in line.split(' -> '))
		prev   = next(points)

		for cur in points:
			cave.update(range2d(prev, cur))
			prev = cur

rocks = set(cave)
maxy = max(map(itemgetter(1), cave))

pour_sand(cave, maxy)
create_image(cave, rocks, 'part1.png')


pour_sand(cave, maxy, True)

# Add rock floor
minx, maxx = min(map(itemgetter(0), cave)) - 1, max(map(itemgetter(0), cave))
for x, y in range2d((minx, maxy  + 2), (maxx + 1, maxy + 2)):
	rocks.add((x, y))

create_image(cave, rocks, 'part2.png')
