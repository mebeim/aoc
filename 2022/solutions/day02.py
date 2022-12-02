#!/usr/bin/env python3

from utils import advent

SCORES1 = (4, 8, 3, 1, 5, 9, 7, 2, 6)
SCORES2 = (3, 4, 8, 1, 5, 9, 2, 6, 7)

advent.setup(2022, 2)
fin = advent.get_input(mode='rb')

table  = bytes.maketrans(b'ABCXYZ', b'036012')
data   = fin.read().translate(table)
score1 = score2 = 0

for line in data.splitlines():
	i = sum(map(int, line.split()))
	score1 += SCORES1[i]
	score2 += SCORES2[i]

advent.print_answer(1, score1)
advent.print_answer(2, score2)
