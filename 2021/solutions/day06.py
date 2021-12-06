#!/usr/bin/env python3

from utils import advent
from collections import defaultdict, Counter

def evolve(fish, days):
	for _ in range(days):
		newfish = defaultdict(int)

		for t, n in fish.items():
			t -= 1

			if t < 0:
				newfish[6] += n
				newfish[8] += n
			else:
				newfish[t] += n

		fish = newfish

	return fish, sum(fish.values())


advent.setup(2021, 6)
fin = advent.get_input()

fish     = Counter(map(int, fin.read().split(',')))
fish, n1 = evolve(fish, 80)
_   , n2 = evolve(fish, 256 - 80)

advent.print_answer(1, n1)
advent.print_answer(2, n2)
