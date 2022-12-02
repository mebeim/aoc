#!/usr/bin/env python3

from utils import advent

advent.setup(2022, 2)
fin = advent.get_input()

score1 = score2 = 0
ord_a = ord('A')
ord_x = ord('X')

for a, b in map(str.split, fin):
	a = ord(a) - ord_a
	b = ord(b) - ord_x

	score1 += b + 1
	score2 += b * 3 + 1

	if a == 0:
		score1 += ((b + 1) % 3) * 3
		score2 += (b + 2) % 3
	elif a == 1:
		score1 += b * 3
		score2 += b
	else:
		score1 += ((b + 2) % 3) * 3
		score2 += (b + 1) % 3

advent.print_answer(1, score1)
advent.print_answer(2, score2)
