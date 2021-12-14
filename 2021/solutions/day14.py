#!/usr/bin/env python3

from utils import advent
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


advent.setup(2021, 14)
fin = advent.get_input()

template = next(fin).rstrip()
rules = {}
next(fin)

for line in map(str.rstrip, fin):
	(a, b), c = line.split(' -> ')
	rules[a, b] = ((a, c), (c, b))

poly = Counter(zip(template, template[1:]))
poly, answer1 = react(poly, rules, 10, template[-1])
poly, answer2 = react(poly, rules, 30, template[-1])

advent.print_answer(1, answer1)
advent.print_answer(2, answer2)
