#!/usr/bin/env python3

from utils import advent

class Number:
	__slots__ = 'value'

	def __init__(self, value):
		self.value = int(value)

def mix(order, times=1):
	numbers, sz = list(order), len(order)

	for _ in range(times):
		for num in order:
			i = numbers.index(num)
			numbers.pop(i)
			numbers.insert((i + num.value) % (sz - 1), num)

	for i, num in enumerate(numbers):
		if num.value == 0:
			break

	return sum(numbers[(i + delta) % sz].value for delta in (1000, 2000, 3000))


advent.setup(2022, 20)

with advent.get_input() as fin:
	order = tuple(map(Number, fin))

answer = mix(order)
advent.print_answer(1, answer)


for num in order:
	num.value *= 811589153

answer = mix(order, 10)
advent.print_answer(2, answer)
