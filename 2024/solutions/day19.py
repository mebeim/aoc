#!/usr/bin/env python3

import sys
from functools import cache, partial


@cache
def count(design, op=any):
	if design == '':
		return True

	matches = filter(design.startswith, towels)
	return op(count(design[len(m):], op) for m in matches)


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

lines = fin.read().splitlines()
towels = lines[0].split(', ')
designs = lines[2:]

total1 = sum(map(count, designs))
print('Part 1:', total1)

total2 = sum(map(partial(count, op=sum), designs))
print('Part 2:', total2)
