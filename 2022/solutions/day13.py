#!/usr/bin/env python3

from json import loads
from functools import cmp_to_key

import sys

def compare(a, b):
	a_is_int = type(a) is int
	b_is_int = type(b) is int

	if a_is_int and b_is_int:
		return a - b

	if a_is_int ^ b_is_int:
		return compare([a], b) if a_is_int else compare(a, [b])

	for x, y in zip(a, b):
		res = compare(x, y)
		if res != 0:
			return res

	return len(a) - len(b)


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

lines   = fin.read().replace('\n\n', '\n').splitlines()
packets = list(map(loads, lines))
pairs   = (packets[i:i + 2] for i in range(0, len(packets), 2))
answer  = sum(i for i, p in enumerate(pairs, 1) if compare(*p) < 0)

print('Part 1:', answer)


packets.extend(([[2]], [[6]]))
packets.sort(key=cmp_to_key(compare))

answer = packets.index([[2]]) + 1
answer *= packets.index([[6]], answer) + 1

print('Part 2:', answer)
