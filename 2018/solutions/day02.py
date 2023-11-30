#!/usr/bin/env python3

import sys
from collections import Counter

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

ids = list(map(str.rstrip, fin))
counts = list(map(Counter, ids))

two_letters = sum(2 in c.values() for c in counts)
three_letters = sum(3 in c.values() for c in counts)

ans = two_letters * three_letters
print('Part 1:', ans)


l = len(ids[0])
assert all(len(x) == l for x in ids)

done = False

for i in range(l):
	seen = set()

	for cur in ids:
		s = cur[:i] + cur[i+1:]

		if s in seen:
			done = True
			break

		seen.add(s)

	if done:
		break

print('Part 2:', s)
