#!/usr/bin/env python3

from utils import advent

advent.setup(2020, 1)
fin = advent.get_input()

numbers = tuple(map(int, fin.readlines()))
compls  = set()

for x in numbers:
	y = 2020 - x

	if x in compls:
		ans = x * y
		break

	compls.add(y)

advent.print_answer(1, ans)


for i, x in enumerate(numbers):
	compls = set()
	yz = 2020 - x

	for y in numbers[i + 1:]:
		z = yz - y

		if y in compls:
			ans = x * y * z
			break

		compls.add(z)

advent.print_answer(2, ans)
