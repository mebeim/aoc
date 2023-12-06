#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 6)
fin = advent.get_input()

lines = read_lines(fin)
ans = 0

times = extract_ints(lines[0])
dists = extract_ints(lines[1])
ways  = [0] * len(dists)

for i, (t, d) in enumerate(zip(times, dists)):
	for hold in range(0, t):
		tot = hold * (t - hold)
		if tot > d:
			ways[i] += 1

ans = prod(ways)

advent.print_answer(1, ans)


times = extract_ints(lines[0].replace(' ', ''))
dists = extract_ints(lines[1].replace(' ', ''))
ways  = [0] * len(dists)

for i, (t, d) in enumerate(zip(times, dists)):
	for hold in range(0, t):
		tot = hold * (t - hold)
		if tot > d:
			ways[i] += 1

ans = prod(ways)
advent.print_answer(2, ans)
