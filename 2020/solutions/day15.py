#!/usr/bin/env python3

import sys

def play(nums, n_turns):
	last_seen = [0] * n_turns
	prev = nums[-1]

	for turn, n in enumerate(nums[:-1], 1):
		last_seen[n] = turn

	for prev_turn in range(len(nums), n_turns):
		cur = prev_turn - last_seen[prev]
		if cur == prev_turn:
			cur = 0

		last_seen[prev] = prev_turn
		prev = cur

	return cur

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

nums = tuple(map(int, fin.read().split(',')))
ans = play(nums, 2020)
print('Part 1:', ans)

ans = play(nums, 30000000)
print('Part 2:', ans)
