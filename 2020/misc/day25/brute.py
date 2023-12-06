#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

with fin:
	A, B = map(int, fin)

x = 1
v = 7

while v != A and v != B:
	v = (v * 7) % 20201227
	x += 1

key = pow(B if v == A else A, x, 20201227)
print('Part 1:', key)
