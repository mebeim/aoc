#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 10)
fin = advent.get_input()
timer_start()

nums = map(int, fin.readlines())
nums = sorted(nums)

prev = nums[0:3]
n1, n3 = 1, 1
for i, n in enumerate(nums[1:], 1):
	# print(i, n, prev)
	if n - 1 == prev[0]:
		n1 += 1
	else:
		for x in prev:
			if n - 3 == x:
				n3 += 1
				break

	prev = nums[i:i+3]

# print(n1, n3)
ans = n1 * n3
advent.print_answer(1, ans)


# @log_calls(True)
@lru_cache(2 ** 24)
def calc(nums, i):
	if i == len(nums) - 1:
		return 1

	tot = 0
	for j in range(i + 1, min(i + 4, len(nums))):
		if nums[j] - nums[i] <= 3:
			tot += calc(nums, j)

	return tot

nums = tuple([0] + nums + [max(nums) + 3])
prev = nums[0]

ans2 = calc(nums, 0)
advent.print_answer(2, ans2)
