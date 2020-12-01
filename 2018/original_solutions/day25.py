#!/usr/bin/env python3

from utils.all import *

advent.setup(2018, 25)
fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

def dist1d(a, b):
	return abs(a - b)

def manhattan(ax, ay, az, at, bx, by, bz, bt):
	return dist1d(ax, bx) + dist1d(ay, by) + dist1d(az, bz) + dist1d(at, bt)

intmat = get_int_matrix(fin, True, as_tuples=True)
consts = defaultdict(set)

for p in intmat:
	matched = set()

	for c, v in consts.items():
		if any(manhattan(*p, *p2) <= 3 for p2 in v):
			matched.add(c)

	if matched:
		c = matched.pop()
		for c2 in matched:
			consts[c].update(consts.pop(c2))
		consts[c].add(p)
	else:
		consts[p].add(p)

# dump_dict(consts)

tot = len(consts)

# 1213 wrong
# 589 wrong
advent.submit_answer(1, tot)

print('Part 2: go get it https://adventofcode.com/2018/day/25')
