#!/usr/bin/env python3

import advent

advent.setup(2019, 1, dry_run=True)
fin = advent.get_input()

nums = map(int, fin.readlines())

nums = list(map(lambda n: n // 3 - 2, nums))
total = sum(nums)

assert total == 3576689
advent.submit_answer(1, total)

for i, n in enumerate(nums):
	while n > 0:
		n = max(n // 3 - 2, 0)
		nums[i] += n

total = sum(nums)

assert total == 5362136
advent.submit_answer(2, total)
