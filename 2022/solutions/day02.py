#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1], 'rb') if len(sys.argv) > 1 else sys.stdin.buffer

SCORES1 = (4, 8, 3, 1, 5, 9, 7, 2, 6)
SCORES2 = (3, 4, 8, 1, 5, 9, 2, 6, 7)

table  = bytes.maketrans(b'ABCXYZ', b'036012')
data   = fin.read().translate(table)
score1 = score2 = 0

for line in data.splitlines():
	i = sum(map(int, line.split()))
	score1 += SCORES1[i]
	score2 += SCORES2[i]

print('Part 1:', score1)
print('Part 2:', score2)
