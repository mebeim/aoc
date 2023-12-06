#!/usr/bin/env python3
#
# Wrapping input numbers into tuples of the form `(original_index, number)`
# instead of a wrapper class. The runtime is comparable.
#

import sys

def mix(order, numbers, times=1):
	sz = len(numbers)

	for _ in range(times):
		for item in order:
			i = numbers.index(item)
			numbers.pop(i)
			i = (i + item[1]) % (sz - 1)
			numbers.insert(i, item)

	for i, item in enumerate(numbers):
		if item[1] == 0:
			break

	return numbers[(i + 1000) % sz][1] + numbers[(i + 2000) % sz][1] + numbers[(i + 3000) % sz][1]


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

with fin:
	order = tuple((i, int(line)) for i, line in enumerate(fin))

numbers = list(order)
ans     = mix(order, numbers)

print('Part 1:', ans)


order   = tuple((i, v * 811589153) for i, v in order)
numbers = list(order)
ans     = mix(order, numbers, 10)

print('Part 2:', ans)
