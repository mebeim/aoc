#!/usr/bin/env python3

import sys
from collections import defaultdict

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

canvas = defaultdict(set)
claim_ids = set()

for line in fin:
	cid, claim = line.split('@')
	cid = int(cid[1:])

	start, size = claim.split(':')
	x, y = map(int, start.split(','))
	w, h = map(int, size.split('x'))

	for i in range(x, x + w):
		for j in range(y, y + h):
			canvas[i, j].add(cid)

	claim_ids.add(cid)

overlapping = sum(map(lambda x: len(x) > 1, canvas.values()))
print('Part 1:', overlapping)


for c in filter(lambda x: len(x) > 1, canvas.values()):
	claim_ids -= c

assert len(claim_ids) == 1

good = claim_ids.pop()
print('Part 2:', good)
