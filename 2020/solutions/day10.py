#!/usr/bin/env python3

from utils import advent
from functools import lru_cache

@lru_cache()
def arrangements(i):
	if i == len(nums) - 1:
		return 1

	tot = 0
	for j in range(i + 1, min(i + 4, len(nums))):
		if nums[j] - nums[i] <= 3:
			tot += arrangements(j)

	return tot


advent.setup(2020, 10)
fin = advent.get_input()

nums = map(int, fin.readlines())
nums = sorted(nums)
dist1, dist3 = 1, 1

for i, cur in enumerate(nums[1:], 1):
	if cur - 1 == nums[i - 1]:
		dist1 += 1
	elif cur - 3 in nums[:i][-3:]:
		dist3 += 1

ans = dist1 * dist3
advent.print_answer(1, ans)


nums = [0] + nums + [max(nums) + 3]
total = arrangements(0)

advent.print_answer(2, total)
