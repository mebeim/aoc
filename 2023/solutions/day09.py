#!/usr/bin/env python3

import sys

def deltas(nums):
	it = iter(nums)
	prev = next(it)

	for n in it:
		yield n - prev
		prev = n

def solve(nums):
	right = left = 0
	sign = 1

	while any(nums):
		right += nums[-1]
		left += sign * nums[0]
		sign = -sign
		nums = list(deltas(nums))

	return right, left


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

total1 = total2 = 0

for line in fin:
	nums = list(map(int, line.split()))
	l, r = solve(nums)
	total1 += l
	total2 += r

print('Part 1:', total1)
print('Part 2:', total2)
