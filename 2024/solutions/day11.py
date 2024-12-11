#!/usr/bin/env python3

import sys
from functools import lru_cache
from math import log10

@lru_cache(None)
def calc(n, blinks=75):
	if blinks == 0:
		return 1

	if n == 0:
		return calc(1, blinks - 1)

	n_digits = int(log10(n)) + 1
	if n_digits % 2 == 0:
		power = 10**(n_digits // 2)
		return calc(n // power, blinks - 1) + calc(n % power, blinks - 1)

	return calc(n * 2024, blinks - 1)


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

numbers = list(map(int, fin.readline().split()))

ans1 = sum(map(lambda n: calc(n, 25), numbers))
print('Part 1:', ans1)

ans2 = sum(map(calc, numbers))
print('Part 2:', ans2)
