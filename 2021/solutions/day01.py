#!/usr/bin/env python3

from utils import advent

advent.setup(2021, 1)
fin = advent.get_input()

nums = tuple(map(int, fin))
tot  = sum(b > a for a, b in zip(nums, nums[1:]))

advent.print_answer(1, tot)


tot  = 0
prev = float('inf')

for cur in map(sum, zip(nums, nums[1:], nums[2:])):
	if cur > prev:
		tot += 1
	prev = cur

advent.print_answer(2, tot)
