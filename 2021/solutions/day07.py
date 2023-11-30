#!/usr/bin/env python3

import sys

def fuel2(nums, x):
	tot = 0
	for n in nums:
		delta = abs(n - x)
		tot += (delta * (delta + 1)) // 2
	return tot


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

nums = list(map(int, fin.readline().split(',')))
nums.sort()

median = nums[len(nums) // 2]
fuel   = sum(abs(x - median) for x in nums)

print('Part 1:', fuel)


mean = sum(nums) // len(nums)
fuel = min(fuel2(nums, mean), fuel2(nums, mean + 1))

print('Part 2:', fuel)
