#!/usr/bin/env python3

from utils import advent
import re
from collections import defaultdict

def intersection(a, b):
	ax1, ax2, ay1, ay2, az1, az2 = a
	bx1, bx2, by1, by2, bz1, bz2 = b

	ix1, ix2 = max(ax1, bx1), min(ax2, bx2)
	iy1, iy2 = max(ay1, by1), min(ay2, by2)
	iz1, iz2 = max(az1, bz1), min(az2, bz2)

	if ix1 < ix2 and iy1 < iy2 and iz1 < iz2:
		return ix1, ix2, iy1, iy2, iz1, iz2

def volume(x1, x2, y1, y2, z1, z2):
	return (x2 - x1 + 1) * (y2 - y1 + 1) * (z2 - z1 + 1)

def volume_small(x1, x2, y1, y2, z1, z2):
	if x1 > 50 or y1 > 50 or z1 > 50 or x2 < -50 or y2 < -50 or z2 < -50:
		return 0

	x1, x2 = max(x1, -50), min(x2, 50)
	y1, y2 = max(y1, -50), min(y2, 50)
	z1, z2 = max(z1, -50), min(z2, 50)

	return volume(x1, x2, y1, y2, z1, z2)


advent.setup(2021, 22)

exp      = re.compile(r'-?\d+')
commands = []
counts   = defaultdict(int)

with advent.get_input() as fin:
	for line in fin:
		cuboid = tuple(map(int, exp.findall(line)))

		for other, count in tuple(counts.items()):
			inter = intersection(cuboid, other)
			if inter is None:
				continue

			counts[inter] -= count

		if line.startswith('on'):
			counts[cuboid] += 1

total = total_small = 0

for cuboid, n in counts.items():
	total       += n * volume(*cuboid)
	total_small += n * volume_small(*cuboid)

advent.print_answer(1, total_small)
advent.print_answer(2, total)
