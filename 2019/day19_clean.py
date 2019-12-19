#!/usr/bin/env python3

import advent
from itertools import product, count
from lib.intcode import intcode_oneshot

def run(inp):
	return next(intcode_oneshot(program, inp))

def bin_search(lo, hi, target):
	best = None

	while hi - lo > 1:
		x = (lo + hi) // 2

		for top in count(0):
			if run((x, top)) == 1:
				break

		for bottom in count(top + 1):
			if run((x, bottom)) == 0:
				break

		if bottom - top < target:
			lo = x
			continue

		y = bottom - target

		for fit in count(1):
			if run((x + fit, y)) == 0:
				break

		if fit > target:
			hi = x
		elif fit < target:
			lo = x
		elif fit == target:
			hi = x
			best = (x, y)

	return best


advent.setup(2019, 19, dry_run=True)
fin = advent.get_input()

program = list(map(int, fin.read().split(',')))
total = sum(map(run, product(range(50), range(50))))

assert total == 152
advent.submit_answer(1, total)

closest = bin_search(10, 5000, 100)
assert closest is not None
answer = closest[0] * 10000 + closest[1]

assert answer == 10730411
advent.submit_answer(2, answer)
