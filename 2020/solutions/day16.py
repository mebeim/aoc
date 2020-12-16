#!/usr/bin/env python3

from utils import advent
import re
from math import prod

class DoubleRange:
	__slots__ = ('a', 'b', 'c', 'd')

	def __init__(self, a, b, c, d):
		self.a, self.b, self.c, self.d = a, b, c, d

	def __contains__(self, value):
		return self.a <= value <= self.b or self.c <= value <= self.d

def parse_input(fin):
	ranges = []
	num_exp = re.compile(r'\d+')

	for line in map(str.rstrip, fin):
		if not line:
			break

		numbers = map(int, num_exp.findall(line))
		ranges.append(DoubleRange(*numbers))

	fin.readline()
	my_ticket = tuple(map(int, fin.readline().split(',')))
	fin.readline()
	fin.readline()

	tickets = []
	for line in fin:
		tickets.append(tuple(map(int, line.split(','))))

	return ranges, my_ticket, tickets

def invalid_fields(ticket):
	for value in ticket:
		if all(value not in rng for rng in ranges):
			yield value

def is_valid(ticket):
	return all(any(v in r for r in ranges) for v in ticket)

def simplify(possible):
	assigned = [None] * len(possible)

	while any(possible):
		for i, poss in enumerate(possible):
			if len(poss) == 1:
				assigned[i] = match = poss.pop()
				break

		for other in possible:
			if match in other:
				other.remove(match)

	return assigned


advent.setup(2020, 16)
fin = advent.get_input()

ranges, my_ticket, tickets = parse_input(fin)
total = sum(map(sum, map(invalid_fields, tickets)))

advent.print_answer(1, total)


tickets.append(my_ticket)
n_fields = len(my_ticket)
possible = [set(range(n_fields)) for _ in range(len(ranges))]

for ticket in filter(is_valid, tickets):
	for rng, poss in zip(ranges, possible):
		for i, value in enumerate(ticket):
			if value not in rng and i in poss:
				poss.remove(i)

indexes = simplify(possible)[:6]
total = prod(my_ticket[i] for i in indexes)

advent.print_answer(2, total)
