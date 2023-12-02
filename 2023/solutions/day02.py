#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

answer1 = answer2 = 0

for line in fin:
	gid, game = line.split(': ')
	gid = int(gid[5:])
	bad = False
	minr = ming = minb = 0

	for turn in game.split('; '):
		r = g = b = 0

		for n, color in map(str.split, turn.split(', ')):
			n = int(n)

			if color == 'red':
				r = n
			elif color == 'green':
				g = n
			else:
				b = n

		bad |= r > 12 or g > 13 or b > 14
		minr = max(r, minr)
		ming = max(g, ming)
		minb = max(b, minb)

	answer1 += gid * (not bad)
	answer2 += minr * ming * minb

print('Part 1:', answer1)
print('Part 2:', answer2)
