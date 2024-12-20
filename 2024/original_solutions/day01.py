#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 1)

fin = advent.get_input()
lines = read_lines(fin)

l = []
r = []

for line in lines:
	a, b = map(int, line.split())
	l.append(a)
	r.append(b)

l.sort()
r.sort()

ans1 = ans2 = 0
for a, b in zip(l, r):
	ans1 += abs(a - b)
	ans2 += a * r.count(a)

advent.print_answer(1, ans1)
advent.print_answer(2, ans2)
