#!/usr/bin/env python3

from operator import itemgetter

from utils import advent

def autorange(a, b):
	return range(a, b - 1, -1) if a > b else range(a, b + 1)

def range2d(a, b):
	ax, ay = a
	bx, by = b

	if ax == bx:
		for y in autorange(ay, by):
			yield ax, y
	elif ay == by:
		for x in autorange(ax, bx):
			yield x, ay
	else:
		raise ValueError('diagonal line?')

def pour(occupied, floory, fill=False):
	p = 500, 0

	if fill and p in occupied:
		return False

	while 1:
		x, y = p
		y += 1

		if y == floory:
			if fill:
				occupied.add(p)
			return fill

		d = (x, y)
		if d not in occupied:
			p = d
			continue

		dl = (x - 1, y)
		if dl not in occupied:
			p = dl
			continue

		dr = (x + 1, y)
		if dr not in occupied:
			p = dr
			continue

		occupied.add(p)
		return True


advent.setup(2022, 14)
occupied = set()

with advent.get_input() as fin:
	for line in fin:
		points = (tuple(map(int, p.split(','))) for p in line.split(' -> '))
		prev   = next(points)

		for cur in points:
			occupied.update(range2d(cur, prev))
			prev = cur

floory = max(map(itemgetter(1), occupied)) + 2

ans = 0
while pour(occupied, floory):
	ans += 1

advent.print_answer(1, ans)


while pour(occupied, floory, True):
	ans += 1

advent.print_answer(2, ans)
