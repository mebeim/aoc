#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 11)
fin = advent.get_input()

ints = extract_ints(data)
ans1 = ans2 = 0

def blink(ints):
	new = []
	for x in ints:
		if x == 0:
			new.append(1)
		else:
			n = str(x)
			l = len(n)
			if l % 2 == 0:
				new.append(int(n[:l // 2]))
				new.append(int(n[l // 2:]))
			else:
				new.append(x * 2024)

	return new

for _ in range(75):
	ints = blink(ints)

ans1 = len(ints)
advent.print_answer(1, ans1)


@lru_cache(None)
def calc(n, blinks=0, limit=75):
	if blinks == limit:
		return 1

	if n == 0:
		return calc(1, blinks + 1, limit)

	s = str(n)
	l = len(s)

	if l % 2 == 0:
		return calc(int(s[:l // 2]), blinks + 1, limit) + calc(int(s[l // 2:]), blinks + 1, limit)

	return calc(n * 2024, blinks + 1, limit)

for i in ints:
	ans2 += calc(i)

advent.print_answer(2, ans2)
