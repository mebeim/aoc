#!/usr/bin/env python3

import advent
from collections import deque

def play(nplayers, max_marble):
	scores = [0] * nplayers
	marbles = deque([0])

	for cur_marble in range(1, max_marble + 1):
		if cur_marble % 23:
			marbles.rotate(-1)
			marbles.append(cur_marble)
		else:
			marbles.rotate(7)
			scores[cur_marble % nplayers] += cur_marble + marbles.pop()
			marbles.rotate(-1)

	return max(scores)


advent.setup(2018, 9, dry_run=True)
fin = advent.get_input()

s = fin.read().split()
nplayers, last_marble = int(s[0]), int(s[6])

winner1 = play(nplayers, last_marble)
# assert winner1 == 398730

advent.submit_answer(1, winner1)

winner2 = play(nplayers, last_marble * 100)
# assert winner2 == 3349635509

advent.submit_answer(2, winner2)
