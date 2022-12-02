#!/usr/bin/env python3
#
# Alternative mathematical solution without lookup tables.
#

score1 = score2 = 0
ord_a = ord('A')
ord_x = ord('X')

with open('input.txt', 'rb') as fin:
	for a, b in map(bytes.split, fin):
		a = ord(a) - ord_a
		b = ord(b) - ord_x

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
