#!/usr/bin/env python3

from utils import advent
import re

def tri(n):
	return n * (n + 1) // 2

def invtri(x):
	return int((x * 2)**0.5)

def search(xmin, xmax, ymin, ymax, v0xmin):
	total = 0

	for v0x in range(v0xmin, xmax + 1):
		for v0y in range(ymin, -ymin):
			x, y   = 0, 0
			vx, vy = v0x, v0y

			while x <= xmax and y >= ymin:
				if x >= xmin and y <= ymax:
					total += 1
					break

				x, y = (x + vx, y + vy)
				vy -= 1

				if vx > 0:
					vx -= 1

	return total


advent.setup(2021, 17)
fin = advent.get_input()

xmin, xmax, ymin, ymax = map(int, re.findall(r'-?\d+', fin.read()))
v0xmin = invtri(xmin)

assert ymin < 0 and ymax < 0
assert tri(v0xmin) == xmin or tri(v0xmin + 1) <= xmax

yhi   = tri(ymin)
total = search(xmin, xmax, ymin, ymax, v0xmin)

advent.print_answer(1, yhi)
advent.print_answer(2, total)
