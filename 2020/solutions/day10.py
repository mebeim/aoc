#!/usr/bin/env python3

import sys
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


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

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
print('Part 1:', ans)

total = arrangements(nums, 0)
print('Part 2:', total)
