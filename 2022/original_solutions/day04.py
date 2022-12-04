#!/usr/bin/env python3

from utils.all import *

advent.setup(2022, 4)

fin = advent.get_input()
lines = get_lines(fin)
ans = 0

for l in lines:
	a, b = l.strip().split(',')
	a1, a2 = map(int, a.split('-'))
	b1, b2 = map(int, b.split('-'))
	# print(a1, a2, b1, b2)

	if a1 <= b1 and a2 >= b2:
		ans += 1
		# print('b in a')
	elif b1 <= a1 and b2 >= a2:
		ans += 1
		# print('a in b')

advent.print_answer(1, ans)


ans = 0
for l in lines:
	a, b = l.strip().split(',')
	a1, a2 = map(int, a.split('-'))
	b1, b2 = map(int, b.split('-'))
	# print(a1, a2, b1, b2)
	o = set(range(a1, a2+1)) & set(range(b1, b2 + 1))
	if o:
		# print(o)
		ans += 1

advent.print_answer(2, ans)
