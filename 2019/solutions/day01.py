#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

nums = map(int, fin.readlines())
nums = tuple(map(lambda n: n // 3 - 2, nums))
total = sum(nums)

print('Part 1:', total)

for n in nums:
	while n > 0:
		n = max(n // 3 - 2, 0)
		total += n

print('Part 2:', total)
