#!/usr/bin/env python3

from utils.all import *

def solve(nums, p2=False):
	lists = [nums]

	while 1:
		deltas = []
		for i in range(1, len(nums)):
			deltas.append(nums[i] - nums[i - 1])

		lists.append(deltas)

		if all(x == 0 for x in deltas):
			break

		nums = deltas

	if not p2:
		prev = 0
		for l in lists[::-1]:
			n = prev + l[-1]
			prev = n

		return n

	prev = 0
	for l in lists[::-1]:
		n = l[0] - prev
		prev = n

	return n


advent.setup(2023, 9)
fin = advent.get_input()
lines = read_lines(fin)

ans1 = ans2 = 0

for line in lines:
	nums = extract_ints(line)
	ans1 += solve(nums)
	ans2 += solve(nums, True)

advent.print_answer(1, ans1)
advent.print_answer(2, ans2)
