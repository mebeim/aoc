#!/usr/bin/env python3

from utils import advent
from itertools import product, cycle
from functools import lru_cache

QUANTUM_ROLLS = tuple(map(sum, product(range(1, 4), range(1, 4), range(1, 4))))

def play1(p1_pos, p2_pos, score_limit):
	rolls = p1_score = p2_score = 0
	die   = cycle(range(1, 101)).__next__

	while 1:
		p1_pos    = (p1_pos + die() + die() + die()) % 10
		p1_score += p1_pos + 1
		rolls    += 3

		if p1_score >= score_limit:
			return rolls, p2_score

		p2_pos    = (p2_pos + die() + die() + die()) % 10
		p2_score += p2_pos + 1
		rolls    += 3

		if p2_score >= score_limit:
			return rolls, p1_score

@lru_cache(maxsize=None)
def play2(my_pos, my_score, other_pos, other_score, score_limit):
	if my_score >= score_limit:
		return 1, 0

	if other_score >= score_limit:
		return 0, 1

	my_wins = other_wins = 0

	for roll in QUANTUM_ROLLS:
		new_pos   = (my_pos + roll) % 10
		new_score = my_score + new_pos + 1

		ow, mw = play2(other_pos, other_score, new_pos, new_score, score_limit)
		my_wins    += mw
		other_wins += ow

	return my_wins, other_wins


advent.setup(2021, 21)

with advent.get_input() as fin:
    p1_pos = int(fin.readline().split()[-1]) - 1
    p2_pos = int(fin.readline().split()[-1]) - 1

rolls, loser_score = play1(p1_pos, p2_pos, 1000)
ans = rolls * loser_score

advent.print_answer(1, ans)


wins = play2(p1_pos, 0, p2_pos, 0, 21)
best = max(wins)

advent.print_answer(2, best)
