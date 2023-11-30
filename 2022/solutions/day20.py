#!/usr/bin/env python3

import sys

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


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

order  = tuple(map(Number, fin))
answer = mix(order)
print('Part 1:', answer)


for num in order:
	num.value *= 811589153

answer = mix(order, 10)
print('Part 2:', answer)
