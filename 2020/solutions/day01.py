#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

numbers = tuple(map(int, fin.readlines()))
compls  = set()

for x in numbers:
	y = 2020 - x

	if x in compls:
		ans = x * y
		break

	compls.add(y)

print('Part 1:', ans)


for i, x in enumerate(numbers):
	compls = set()
	yz = 2020 - x

	for y in numbers[i + 1:]:
		z = yz - y

		if y in compls:
			ans = x * y * z
			break

		compls.add(z)

print('Part 2:', ans)
