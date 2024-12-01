#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

total1 = total2 = 0

left = []
right = []

for line in fin:
	l, r = map(int, line.split())
	left.append(l)
	right.append(r)

left.sort()
right.sort()

for l, r in zip(left, right):
	total1 += abs(l - r)
	total2 += l * right.count(l)

print('Part 1:', total1)
print('Part 2:', total2)
