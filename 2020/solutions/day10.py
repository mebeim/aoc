#!/usr/bin/env python3

from utils import advent
from functools import lru_cache

def arrangements(nums, i):
	@lru_cache()
	def real_fn(i):
		if i == len(nums) - 1:
			return 1

		tot = 0
		for j in range(i + 1, min(i + 4, len(nums))):
			if nums[j] - nums[i] <= 3:
				tot += real_fn(j)

		return tot

	return real_fn(i)


advent.setup(2020, 10)
fin = advent.get_input()

nums = sorted(map(int, fin))
nums = [0] + nums + [max(nums) + 3]
dist1 = dist3 = 0

for cur, nxt in zip(nums, nums[1:]):
    delta = nxt - cur

    if delta == 1:
        dist1 += 1
    elif delta == 3:
        dist3 += 1

ans = dist1 * dist3
advent.print_answer(1, ans)

total = arrangements(nums, 0)
advent.print_answer(2, total)
