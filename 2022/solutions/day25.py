#!/usr/bin/env python3

import sys

VALUES = {'=': -2, '-': -1, '0': 0, '1': 1, '2': 2}

def base10(n):
	power = 5 ** (len(n) - 1)
	res = 0

	for digit in n:
		res += VALUES[digit] * power
		power //= 5

	return res

def snafu(n):
	res = ''

	while n:
		n, digit = divmod(n, 5)
		res += '012=-'[digit]
		n += digit > 2

	return res[::-1]


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

answer = snafu(sum(map(base10, fin.read().split())))
print('Part 1:', answer)
