#!/usr/bin/env python3

import sys
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


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

fish     = Counter(map(int, fin.read().split(',')))
fish, n1 = evolve(fish, 80)
_   , n2 = evolve(fish, 256 - 80)

print('Part 1:', n1)
print('Part 2:', n2)
