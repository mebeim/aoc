#!/usr/bin/env python3

from utils import advent
import re

def invtri(x):
	return int((x * 2)**0.5)

def search(xmin, xmax, ymin, ymax, v0xmin):
	total = 0
	yhi   = 0

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

				if y > yhi:
					yhi = y

	return yhi, total


advent.setup(2021, 17)
fin = advent.get_input()

xmin, xmax, ymin, ymax = map(int, re.findall(r'-?\d+', fin.read()))
assert ymin < 0 and ymax < 0

v0xmin = invtri(xmin)

# Here, if the following assumption holds (tri(n) == n-th triangular number):
#
#     assert tri(v0xmin) == xmin or tri(v0xmin + 1) <= xmax
#
# we could simply calculate yhi = tri(ymin) = ymin * (ymin + 1) // 2. To be
# safer though, and since we need to do a brute-force for P2 anyway, I have also
# integrated P1's calculation into search().

yhi, total = search(xmin, xmax, ymin, ymax, v0xmin)

advent.print_answer(1, yhi)
advent.print_answer(2, total)
