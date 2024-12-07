#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 7)
fin = advent.get_input()

lines = read_lines(fin)
ans1 = ans2 = 0


def check(nums, res):
	spots = len(nums) - 1
	# print(nums, res, spots)

	for mask in range(1 << (spots + 1)):
		total = nums[0]

		for j in range(spots):
			if mask & (1 << j):
				total += nums[j + 1]
			else:
				total *= nums[j + 1]

			if total > res:
				break

			# print('j', j, 'total', total)

		if total == res:
			return res

	return 0


from math import log10

def chk(res, acc, nums):
	if acc > res:
		return False

	if not nums:
		return acc == res

	n, *nums = nums
	if chk(res, acc + n, nums):
		return True

	if chk(res, acc * n, nums):
		return True

	digits = int(log10(n)) + 1
	if chk(res, acc * 10**digits + n, nums):
		return True

	return False


for line in lines:
	res, nums = line.split(': ')
	res = int(res)
	nums = list(map(int, nums.strip().split()))

	ans1 += check(nums, res)

	if chk(res, nums[0], nums[1:]):
		ans2 += res

advent.print_answer(1, ans1)

# 9440677148120 wrong
# 146111650243239 wrong
advent.print_answer(2, ans2)
