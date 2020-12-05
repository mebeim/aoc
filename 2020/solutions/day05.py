#!/usr/bin/env python3

from utils import advent
from itertools import product

advent.setup(2020, 5)
fin = advent.get_input()

table = str.maketrans('BFRL', '1010')
seats = fin.read().translate(table).splitlines()
seats = list(map(lambda s: (int(s[:7], 2), int(s[7:], 2)), seats))
max_id = 0

for row, col in seats:
	seat_id = row * 8 + col

	if seat_id > max_id:
		max_id = seat_id

advent.print_answer(1, max_id)


seats = set(seats)

for r, c in product(range(1, 127), range(1, 7)):
	if (r, c) not in seats and (r, c - 1) in seats and (r, c + 1) in seats:
		my_id = r * 8 + c
		break

advent.print_answer(2, my_id)
