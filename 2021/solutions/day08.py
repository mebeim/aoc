#!/usr/bin/env python3

import sys

def deduce_mapping(patterns):
	p2d = {} # pattern to digit

	for p, plen in patterns:
		if plen == 2:
			p2d[p] = 1
		elif plen == 3:
			p2d[p] = 7
		elif plen == 4:
			p2d[p] = 4
		elif plen == 7:
			p2d[p] = 8

	d2p = {v: k for k, v in p2d.items()} # digit to pattern

	for p, plen in patterns:
		if p in p2d:
			continue

		if plen == 5:
			# 2 or 3 or 5
			if len(p & d2p[1]) == 2:
				p2d[p] = 3
			elif len(p & d2p[4]) == 3:
				p2d[p] = 5
			else:
				p2d[p] = 2
		else:
			# 0 or 6 or 9
			if len(p & d2p[4]) == 4:
				p2d[p] = 9
			elif len(p & d2p[7]) == 2:
				p2d[p] = 6
			else:
				p2d[p] = 0

	return p2d


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

total    = 0
count    = 0
to_count = {2, 4, 3, 7}

for line in fin:
	patterns, digits = map(str.split, line.split('|'))
	patterns = tuple(map(lambda p: (frozenset(p), len(p)), patterns))
	digits   = tuple(map(lambda p: (frozenset(p), len(p)), digits))
	p2d      = deduce_mapping(patterns)

	count += sum(l in to_count for _, l in digits)
	total += p2d[digits[0][0]] * 1000
	total += p2d[digits[1][0]] * 100
	total += p2d[digits[2][0]] * 10
	total += p2d[digits[3][0]]

print('Part 1:', count)
print('Part 2:', total)
