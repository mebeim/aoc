#!/usr/bin/env python3

from utils import advent

advent.setup(2019, 1, dry_run=True)
fin = advent.get_input()

nums = map(int, fin.readlines())
nums = tuple(map(lambda n: n // 3 - 2, nums))
total = sum(nums)

assert total == 3576689
advent.submit_answer(1, total)

for n in nums:
	while n > 0:
		n = max(n // 3 - 2, 0)
		total += n

assert total == 5362136
advent.submit_answer(2, total)
