#!/usr/bin/env python3

import advent
from itertools import islice

advent.setup(2019, 4, dry_run=True)
fin = advent.get_input()

lo, hi = map(int, fin.read().split('-'))
n1 = n2 = 0

for pwd in range(lo, hi + 1):
	digits = str(pwd)
	pairs = tuple(zip(digits, digits[1:]))

	if all(a <= b for a, b in pairs) and any(a == b for a, b in pairs):
		n1 += 1

		digits = 'x' + digits + 'x'
		isolated_pairs = zip(digits, digits[1:], digits[2:], digits[3:])

		if any(a != b and b == c and c != d for a, b, c, d in isolated_pairs):
			n2 += 1

assert n1 == 1767
advent.submit_answer(1, n1)

assert n2 == 1192
advent.submit_answer(2, n2)
