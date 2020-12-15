#!/usr/bin/env python3

from utils import advent

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

advent.setup(2020, 15)
fin = advent.get_input()

nums = tuple(map(int, fin.read().split(',')))
ans = play(nums, 2020)
advent.print_answer(1, ans)

ans = play(nums, 30000000)
advent.print_answer(2, ans)
