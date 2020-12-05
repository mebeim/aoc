#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 5)
fin = advent.get_input()
# eprint(*fin, sep=''); fin.seek(0, 0)
timer_start()

lines = get_lines(fin)

ans = 0
for l in lines:
	l = l.strip().replace('B', '1').replace('F', '0').replace('R', '1').replace('L', '0')
	a = int(l[:7], 2)
	b = int(l[7:], 2)
	id = a * 8 + b
	if id > ans:
		ans = id

advent.submit_answer(1, ans)


s = set()
for l in lines:
	l = l.strip().replace('B', '1').replace('F', '0').replace('R', '1').replace('L', '0')
	a = int(l[:7], 2)
	b = int(l[7:], 2)
	s.add((a, b))

for r in range(1, 127):
	for c in range(1, 7):

		if (r, c) not in s and (r, c-1) in s and (r, c+1) in s:
			print(r, c)
			ans2 = r * 8 + c

advent.submit_answer(2, ans2)
