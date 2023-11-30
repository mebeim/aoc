#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

deltas = list(map(int, fin.readlines()))
done = False
freq = 0
seen = set()
seen.add(0)

for d in deltas:
	freq += d

	if not done and freq in seen:
		done = True

	seen.add(freq)

print('Part 1:', freq)

while not done:
	for d in deltas:
		freq += d

		if freq in seen:
			done = True
			break

		seen.add(freq)

print('Part 2:', freq)
