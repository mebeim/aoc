#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 19)
fin = advent.get_input()
lines = read_lines(fin)


@selective_cache('design')
def solve(design, towels):
	if design == '':
		return True

	matches = []
	for t in towels:
		if design.startswith(t):
			matches.append(t)

	for m in matches:
		if solve(design[len(m):], towels):
			return True

	return False


@selective_cache('design')
def count(design, towels):
	if design == '':
		return 1

	matches = []
	for t in towels:
		if design.startswith(t):
			matches.append(t)

	return sum(count(design[len(m):], towels) for m in matches)


ans1 = ans2 = 0

towels = list(lines[0].split(', '))
designs = lines[2:]

ans1 = sum(solve(d, towels) for d in designs)
advent.print_answer(1, ans1)

ans2 = sum(count(d, towels) for d in designs)
advent.print_answer(2, ans2)
