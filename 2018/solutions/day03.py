#!/usr/bin/env python3

from utils import advent
from collections import defaultdict

advent.setup(2018, 3, dry_run=True)
fin = advent.get_input()

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

assert overlapping == 118322
advent.submit_answer(1, overlapping)

for c in filter(lambda x: len(x) > 1, canvas.values()):
	claim_ids -= c

assert len(claim_ids) == 1

good = claim_ids.pop()

assert good == 1178
advent.submit_answer(2, good)
