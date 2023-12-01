#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 1)

fin = advent.get_input()
lines = read_lines(fin)

ans = 0
nums = {
	'zero' : 0,
	'one'  : 1,
	'two'  : 2,
	'three': 3,
	'four' : 4,
	'five' : 5,
	'six'  : 6,
	'seven': 7,
	'eight': 8,
	'nine' : 9,
}

for l in lines:
	cs = re.findall('\d', l)
	ans += int(cs[0] + cs[-1])

advent.print_answer(1, ans)

ans = 0

for l in lines:
	p = []

	for i, c in enumerate(l):
		if c.isdigit():
			p.append(int(c))
		else:
			for n in nums:
				if l[i:].startswith(n):
					p.append(nums[n])
					break

	ans += p[0] * 10 + p[-1]

advent.print_answer(2, ans)
