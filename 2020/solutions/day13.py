#!/usr/bin/env python3

from utils import advent
from math import inf, gcd
from itertools import count

def lcm(a, b): # math.lcm() on Python >= 3.9
	return a * b // gcd(a, b)


advent.setup(2020, 13)
fin = advent.get_input()

# from io import StringIO
# fin = StringIO('''\
# 0
# 7,13,x,x,59,x,31,19
# ''')

arrival = int(fin.readline())
raw = fin.readline().strip().split(',')

buses = []
for i, t in enumerate(raw):
	if t != 'x':
		buses.append((i, int(t)))

best = inf
for _, period in buses:
	n = arrival // period + (arrival % period != 0)
	wait = n * period - arrival

	if wait < best:
		best = wait
		best_p = period

ans = best_p * best
advent.print_answer(1, ans)


time, step = buses[0]
for delta, period in buses[1:]:
	for time in count(time, step):
		if (time + delta) % period == 0:
			break

	step = lcm(step, period)

advent.print_answer(2, time)
