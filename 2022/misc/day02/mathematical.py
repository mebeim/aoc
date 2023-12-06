#!/usr/bin/env python3
#
# Alternative mathematical solution without lookup tables.
#

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1], 'rb') if len(sys.argv) > 1 else sys.stdin.buffer

score1 = score2 = 0
ord_a = b'A'[0]
ord_x = b'X'[0]

with fin:
	for line in fin:
		a = line[0] - ord_a
		b = line[2] - ord_x

		score1 += b + 1
		score2 += b * 3 + 1

		if a == 0:
			score1 += ((b + 1) % 3) * 3
			score2 += (b + 2) % 3
		elif a == 1:
			score1 += b * 3
			score2 += b
		else:
			score1 += ((b + 2) % 3) * 3
			score2 += (b + 1) % 3

print('Part 1:', score1)
print('Part 2:', score2)
