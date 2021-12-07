#!/usr/bin/env python3

from utils import advent

def fuel2(nums, x):
	tot = 0
	for n in nums:
		delta = abs(n - x)
		tot += (delta * (delta + 1)) // 2
	return tot


advent.setup(2021, 7)
fin = advent.get_input()

nums = list(map(int, fin.readline().split(',')))
nums.sort()

median = nums[len(nums) // 2]
fuel   = sum(abs(x - median) for x in nums)

advent.print_answer(1, fuel)


mean = sum(nums) // len(nums)
fuel = min(fuel2(nums, mean), fuel2(nums, mean + 1))

advent.print_answer(2, fuel)
