#!/usr/bin/env python3

import sys
from collections import Counter, defaultdict

def react(poly, rules, n, last):
	for _ in range(n):
		newpoly = defaultdict(int)

		for pair in poly:
			products = rules.get(pair)

			if products:
				n = poly[pair]
				newpoly[products[0]] += n
				newpoly[products[1]] += n
			else:
				newpoly[pair] = poly[pair]

		poly = newpoly

	counts = defaultdict(int, {last: 1})
	for (a, _), n in poly.items():
		counts[a] += n

	return poly, max(counts.values()) - min(counts.values())


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

template = next(fin).rstrip()
rules = {}
next(fin)

for line in map(str.rstrip, fin):
	(a, b), c = line.split(' -> ')
	rules[a, b] = ((a, c), (c, b))

poly = Counter(zip(template, template[1:]))
poly, answer1 = react(poly, rules, 10, template[-1])
poly, answer2 = react(poly, rules, 30, template[-1])

print('Part 1:', answer1)
print('Part 2:', answer2)
