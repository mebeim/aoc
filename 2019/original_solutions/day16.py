#!/usr/bin/env python3

from utils.all import *

advent.setup(2019, 16)
fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

lines = get_lines(fin)
orig_nums = list(map(int, lines[0].strip()))

p = [0, 1, 0, -1]

def rep(p, n):
	l = [0] * len(p) * n
	for i in range(len(p)):
		for j in range(n):
			l[i * n + j] = p[i]

	return l[1:] + [l[0]]

from itertools import cycle

nums = orig_nums[:]
for _ in range(100):
	oldnums = nums[:]

	for mul in range(1, len(nums) + 1):
		pp = rep(p, mul)
		# eprint(mul, pp)
		cur = 0

		for n, x in zip(oldnums, cycle(pp)):
			# log('{}*{}, ', n, x)
			cur += n * x
		# eprint()

		nums[mul-1] = abs(cur) % 10

ans = ''.join(map(str, nums[:8]))
advent.submit_answer(1, ans)


nums = orig_nums[:] * 10000
# nums = list(map(int, '03036732577212944063491565474664')) * 10000

skip = int(''.join(map(str, nums[:7])))
nums = nums[skip:]
L = len(nums)

for step in range(100):
	for i in range(L - 2, -1, -1):
		nums[i] += nums[i+1]
		nums[i] %= 10

ans2 = ''.join(map(str, nums[:8]))
advent.submit_answer(2, ans2)
