#!/usr/bin/env python3
#
# This solution should *in theory* be faster. However, given the amount of calls
# to .index() and .rotate(), and the nature of deques, it is actually slightly
# slower than using "nurmal" lists. It is *a lot* slower with PyPy.
#

from collections import deque

def mix(order, numbers, times=1):
	sz = len(numbers)

	for _ in range(times):
		for item in order:
			numbers.rotate(-numbers.index(item))
			numbers.popleft()
			numbers.rotate(-item[1])
			numbers.appendleft(item)

	for i, item in enumerate(numbers):
		if item[1] == 0:
			break

	return numbers[(i + 1000) % sz][1] + numbers[(i + 2000) % sz][1] + numbers[(i + 3000) % sz][1]


advent.setup(2022, 20)

with open('input.txt') as fin:
	order = tuple((i, int(line)) for i, line in enumerate(fin))

numbers = deque(order)
answer  = mix(order, numbers)

advent.print_answer(1, answer)


order   = tuple((i, v * 811589153) for i, v in order)
numbers = deque(order)
answer  = mix(order, numbers, 10)

advent.print_answer(2, answer)
