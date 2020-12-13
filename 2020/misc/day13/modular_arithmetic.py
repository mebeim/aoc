#!/usr/bin/env python3
#
# Alternative "purely mathematical" solution.
#

from math import inf
from functools import reduce
from operator import mul, itemgetter

def egcd(a, b):
	if a == 0:
		return (b, 0, 1)

	g, y, x = egcd(b % a, a)
	return (g, x - (b // a) * y, y)

def modinv(x, m):
	g, inv, y = egcd(x, m)
	assert g == 1, 'modular inverse does not exist'
	return inv % m

def chinese_remainder_theorem(equations):
	x = 0
	P = reduce(mul, map(itemgetter(1), equations))

	for ai, pi in equations:
		ni = P // pi
		inv = modinv(ni, pi) # pow(ni, -1, pi) on Python >= 3.8
		x = (x + ai * ni * inv) % P

	return x

fin = open('input.txt')

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
advent.print_answer(1, ans)

time = chinese_remainder_theorem(buses)
advent.print_answer(2, time)
