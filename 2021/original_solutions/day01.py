#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 1)
fin = advent.get_input()

ints = get_ints(fin)
ans = 0

for a, b in zip(ints, ints[1:]):
	if b > a: ans += 1

advent.submit_answer(1, ans)

ans = 0
prev = None

for a, b, c in zip(ints, ints[1:], ints[2:]):
	s = a + b + c
	if prev is not None and s > prev:
		ans += 1
	prev = s

advent.submit_answer(2, ans)
