#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

overlap = full_overlap = 0

for line in fin:
	a, b   = line.strip().split(',')
	a1, a2 = map(int, a.split('-'))
	b1, b2 = map(int, b.split('-'))

	o1 = max(a1, b1)
	o2 = min(a2, b2)

	if o2 >= o1:
		overlap += 1
		if o1 == a1 and o2 == a2 or o1 == b1 and o2 == b2:
			full_overlap += 1

print('Part 1:', full_overlap)
print('Part 2:', overlap)
