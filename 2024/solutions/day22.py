#!/usr/bin/env pypy3

import sys
from collections import defaultdict


def transform(n):
	for _ in range(2000):
		n = ((n << 6) ^ n) & 0xffffff
		n = ((n >> 5) ^ n) & 0xffffff
		n = ((n << 11) ^ n) & 0xffffff

	return n


def map_sequence(n):
	key = 0
	prev = n % 10
	value_map = {}

	for i in range(2000):
		n = ((n << 6) ^ n) & 0xffffff
		n = ((n >> 5) ^ n) & 0xffffff
		n = ((n << 11) ^ n) & 0xffffff

		value = n % 10
		diff = value - prev
		prev = value

		key = ((key & 0x7fff) << 5) | (diff + 10)
		if key not in value_map:
			value_map[key] = value

	return value_map


def solve(numbers):
	total_value = defaultdict(int)

	for value_map in map(map_sequence, numbers):
		for seq, value in value_map.items():
			total_value[seq] += value

	return max(total_value.values())


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

numbers = list(map(int, fin.read().splitlines()))
ans1 = sum(map(transform, numbers))
print('Part 1:', ans1)

ans2 = solve(numbers)
print('Part 2:', ans2)
