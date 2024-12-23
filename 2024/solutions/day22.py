#!/usr/bin/env pypy3

import sys
from collections import defaultdict


def map_sequence(n):
	diff_map = {}
	prev = n % 10
	key = 0

	for i in range(2000):
		n = ((n << 6) ^ n) & 0xffffff
		n = ((n >> 5) ^ n) & 0xffffff
		n = ((n << 11) ^ n) & 0xffffff

		value = n % 10

		if i >= 3:
			# Use key as a compact hash of the last 4 diff values, using 5 bits
			# per value ([-9, 9] -> [1, 19]) with 0 meaning "no value".
			key = ((key & 0x7fff) << 5) | (value - prev + 10)
			if key not in diff_map:
				diff_map[key] = value

		prev = value

	return n, diff_map


def solve(numbers):
	total_final_values = 0
	sequence_value = defaultdict(int)

	for final_value, diff_map in map(map_sequence, numbers):
		total_final_values += final_value

		for seq, value in diff_map.items():
			sequence_value[seq] += value

	return total_final_values, max(sequence_value.values())


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

numbers = list(map(int, fin.read().splitlines()))

ans1, ans2 = solve(numbers)
print('Part 1:', ans1)
print('Part 2:', ans2)
