#!/usr/bin/env python3

from utils import advent
import sys

from blist import blist

advent.setup(2018, 9)
fin = advent.get_input()

##################################################

s = fin.read().split()
nplayers, last_marble = int(s[0]), int(s[6])

marbles = blist([0])
cur_marble = 0
cur_idx = 0
cur_player = 1
scores = {}

# nplayers = 10
# last_marble = 1618

for i in range(1, nplayers+1):
	scores[i] = 0

while cur_marble < last_marble:

	cur_marble += 1

	# sys.stdout.write(str(cur_marble) + '\r')

	if cur_marble % 23 != 0:
		cur_idx = (cur_idx + 1) % len(marbles) + 1
		marbles.insert(cur_idx, cur_marble)
	else:
		cur_idx = (cur_idx - 7) % len(marbles)
		points = cur_marble + marbles.pop(cur_idx)

		scores[cur_marble % nplayers + 1] += points

		# print('\n>>>', cur_marble, points, last_marble)


winner_score = max(scores.values())
advent.submit_answer(1, winner_score)


marbles = blist([0])
cur_marble = 0
cur_idx = 0
cur_player = 1
scores = {}

last_marble *= 100

for i in range(1, nplayers+1):
	scores[i] = 0

while cur_marble < last_marble:

	cur_marble += 1

	# sys.stdout.write(str(cur_marble) + '\r')

	if cur_marble % 23 != 0:
		cur_idx = (cur_idx + 1) % len(marbles) + 1
		marbles.insert(cur_idx, cur_marble)
	else:
		cur_idx = (cur_idx - 7) % len(marbles)
		points = cur_marble + marbles.pop(cur_idx)

		scores[cur_marble % nplayers + 1] += points


winner_score = max(scores.values())
advent.submit_answer(2, winner_score)
