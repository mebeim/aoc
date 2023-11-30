#!/usr/bin/env python3

import sys
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


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

s = fin.read().split()
nplayers, last_marble = int(s[0]), int(s[6])

winner1 = play(nplayers, last_marble)
print('Part 1:', winner1)

winner2 = play(nplayers, last_marble * 100)
print('Part 2:', winner2)
