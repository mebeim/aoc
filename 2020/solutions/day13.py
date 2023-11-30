#!/usr/bin/env python3

import sys
from math import inf, gcd
from itertools import count

def lcm(a, b):
	return a * b // gcd(a, b)


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

arrival = int(fin.readline())
raw = fin.readline().strip().split(',')

buses = []
for i, v in filter(lambda iv: iv[1] != 'x', enumerate(raw)):
	buses.append((i, int(v)))

best = inf
for _, period in buses:
	n = arrival // period + (arrival % period != 0)
	wait = n * period - arrival

	if wait < best:
		best = wait
		best_p = period

ans = best_p * best
print('Part 1:', ans)


time, step = buses[0]
for delta, period in buses[1:]:
	for time in count(time, step):
		if (time + delta) % period == 0:
			break

	step = lcm(step, period) # math.lcm() on Python >= 3.9

print('Part 2:', time)
