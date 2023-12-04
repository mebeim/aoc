#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 4)

fin = advent.get_input()
lines = read_lines(fin)

ans = 0
cards = []

for line in lines:
	line = line.split(': ')[1]
	a, b = line.split(' | ')
	ia = set(extract_ints(a))
	ib = set(extract_ints(b))

	cards.append((ia, ib))
	n = 0
	for a in ia:
		if a in ib:
			if n:
				n *= 2
			else:
				n += 1

	ans += n

advent.print_answer(1, ans)


copies = [0] * len(cards)

for i, (ia, ib) in enumerate(cards):
	matches = sum(a in ib for a in ia)

	for j in range(i + 1, min(len(cards), i + matches + 1)):
		copies[j] += 1 + copies[i]

n = len(cards) + sum(copies)
advent.print_answer(2, n)
