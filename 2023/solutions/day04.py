#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

matches = []

for line in fin:
	winners, numbers = line[line.find(':') + 1:].split('|')
	winners = set(map(int, winners.split()))
	numbers = set(map(int, numbers.split()))
	matches.append(len(numbers & winners))

score = sum(int(2**(n - 1)) for n in matches)
print('Part 1:', score)


copies = [1] * len(matches)

for i, n in enumerate(matches):
	for j in range(i + 1, i + n + 1):
		copies[j] += copies[i]

total = sum(copies)
print('Part 2:', total)
