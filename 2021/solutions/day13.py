#!/usr/bin/env python3

from utils import advent
from operator import itemgetter

def fold(sheet, axis, vertical=False):
	folded = set()

	for x, y in sheet:
		if vertical:
			if x > axis:
				x = axis - (x - axis)
		elif y > axis:
			y = axis - (y - axis)

		folded.add((x, y))

	return folded

def print_sheet(sheet):
	maxx = max(map(itemgetter(0), sheet))
	maxy = max(map(itemgetter(1), sheet))

	out = ''
	for y in range(maxy + 1):
		for x in range(maxx + 1):
			out += '#' if (x, y) in sheet else ' '
		out += '\n'

	print(out, end='')


advent.setup(2021, 13)
fin = advent.get_input()

sheet = set()

for line in fin:
	if line == '\n':
		break

	sheet.add(tuple(map(int, line.split(','))))

line     = next(fin)
axis     = int(line[line.index('=') + 1:])
sheet    = fold(sheet, axis, 'x' in line)
n_points = len(sheet)

advent.print_answer(1, n_points)


for line in fin:
	axis  = int(line[line.index('=') + 1:])
	sheet = fold(sheet, axis, 'x' in line)

print('Part 2:')
print_sheet(sheet)
