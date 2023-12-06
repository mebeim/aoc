#!/usr/bin/env python3

import sys
from math import ceil, floor, prod

def solve(t, d):
	delta = (t**2 - 4*d)**0.5
	lo, hi = (t - delta) / 2, (t + delta) / 2
	return ceil(hi) - floor(lo) - 1


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

lines = fin.readlines()

times = map(int, lines[0][9:].split())
dists = map(int, lines[1][9:].split())
ans = prod(map(solve, times, dists))
print('Part 1:', ans)

time = int(lines[0][9:].replace(' ', ''))
dist = int(lines[1][9:].replace(' ', ''))
ans  = solve(time, dist)
print('Part 2:', ans)
