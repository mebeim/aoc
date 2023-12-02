#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

answer1 = answer2 = 0

for line in fin:
	gid, game = line.split(': ')
	gid = int(gid[5:])
	maxr = maxg = maxb = 0

	for turn in game.split('; '):
		for n, color in map(str.split, turn.split(', ')):
			n = int(n)

			if color == 'red':
				maxr = max(n, maxr)
			elif color == 'green':
				maxg = max(n, maxg)
			else:
				maxb = max(n, maxb)

	answer1 += gid * (maxr <= 12 and maxg <= 13 and maxb <= 14)
	answer2 += maxr * maxg * maxb

print('Part 1:', answer1)
print('Part 2:', answer2)
