#!/usr/bin/env python3

import sys
from math import ceil, sqrt

def bsgs(base, n, p):
	'''Calculate the discrete logarithm modulo p of n to the given base, using
	the baby-step giant-step algorithm. Note: p must be prime, n must be a
	primitive root modulo p.
	'''

	m     = ceil(sqrt(p))
	table = {pow(base, i, p): i for i in range(m)}
	inv   = pow(base, (p - 2) * m, p) # base^(-m) mod p == base^(m*(p-2)) assuming p is prime
	res   = None

	for i in range(m):
		y = (n * pow(inv, i, p)) % p
		if y in table:
			res = i * m + table[y]
			break

	return res


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

A, B = map(int, fin)
a    = bsgs(7, A, 20201227)
key  = pow(B, a, 20201227)

print('Part 1:', key)
