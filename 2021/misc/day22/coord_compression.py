#!/usr/bin/env python3
#
# Day 22 (part 2 only) using coordinate compression.
# Runtime is pretty ridicolous at around 3m 30s for CPython 3.9.2 on my machine.
# PyPy 7.3.5 on the other hand runs this in a decent time of about 6.5 seconds.
#

import re
import resource
from bisect import bisect_left

# Limit memory usage to 8GB just to be sure... the `space` list below will be huge.
resource.setrlimit(resource.RLIMIT_AS, (8 * 2**30,) * 2)

commands = []
xs, ys, zs = [], [], []

with open('input.txt') as fin:
	for line in fin:
		on = int(line.startswith('on'))
		x1, x2, y1, y2, z1, z2 = tuple(map(int, re.findall(r'-?\d+', line)))
		commands.append((on, x1, x2 + 1, y1, y2 + 1, z1, z2 + 1))
		xs.extend((x1, x2 + 1))
		ys.extend((y1, y2 + 1))
		zs.extend((z1, z2 + 1))

xs.sort()
ys.sort()
zs.sort()

total = 0
space = [[[0] * len(zs) for _ in range(len(ys))] for _ in range(len(xs))]

for on, x1, x2, y1, y2, z1, z2 in commands:
	rank_x1, rank_x2 = bisect_left(xs, x1), bisect_left(xs, x2)
	rank_y1, rank_y2 = bisect_left(ys, y1), bisect_left(ys, y2)
	rank_z1, rank_z2 = bisect_left(zs, z1), bisect_left(zs, z2)

	for i in range(rank_x1, rank_x2):
		for j in range(rank_y1, rank_y2):
			for k in range(rank_z1, rank_z2):
				space[i][j][k] = on

for i in range(len(xs) - 1):
	for j in range(len(ys) - 1):
		for k in range(len(zs) - 1):
			total += space[i][j][k] * (xs[i + 1] - xs[i]) * (ys[j + 1] - ys[j]) * (zs[k + 1] - zs[k])

print('Part 2:', total)
