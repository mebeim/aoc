#!/usr/bin/env python3

from utils.all import *

advent.setup(2019, 1)

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

nums = get_ints(fin, True)

f = []

for n in nums:
	f.append(n // 3 - 2)

ans = sum(f)
advent.submit_answer(1, ans)

nums = f[:]

for i in range(len(nums)):
	# eprint(i)
	x = nums[i] // 3 - 2
	while x > 0:
		f[i] += x
		x = x // 3 - 2

ans2 = sum(f)
advent.submit_answer(2, ans2)
