#!/usr/bin/env python3

from utils import advent
from itertools import islice

advent.setup(2019, 4)
fin = advent.get_input()

lo, hi = map(int, fin.read().split('-'))
n_valid1 = 0
n_valid2 = 0

for pwd in range(lo, hi + 1):
	digits = str(pwd)
	pairs = tuple(zip(digits, digits[1:]))

	if all(a <= b for a, b in pairs) and any(a == b for a, b in pairs):
		n_valid1 += 1

		digits = 'x' + digits + 'x'
		quadruplets = zip(digits, digits[1:], digits[2:], digits[3:])

		if any(a != b and b == c and c != d for a, b, c, d in quadruplets):
			n_valid2 += 1

advent.print_answer(1, n_valid1)
advent.print_answer(2, n_valid2)
