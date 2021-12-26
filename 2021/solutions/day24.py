#!/usr/bin/env python3

from utils import advent
from collections import deque
from functools import reduce

def skip(file, n):
	for _ in range(n):
		next(file)

def get_constraints(fin):
	constraints = []
	stack = deque()

	for i in range(14):
		skip(fin, 4)
		op = next(fin).rstrip()
		assert op.startswith('div z '), 'Invalid input!'

		if op == 'div z 1':
			skip(fin, 10)
			op = next(fin)
			assert op.startswith('add y '), 'Invalid input!'

			a = int(op.split()[-1])
			stack.append((i, a))
			skip(fin, 2)
		else:
			op = next(fin)
			assert op.startswith('add x '), 'Invalid input!'

			b = int(op.split()[-1])
			j, a = stack.pop()
			constraints.append((i, j, a + b))
			skip(fin, 12)

	return constraints

def find_max_min(constraints):
	nmax = [0] * 14
	nmin = [0] * 14

	for i, j, diff in constraints:
		if diff > 0:
			nmax[i], nmax[j] = 9, 9 - diff
			nmin[i], nmin[j] = 1 + diff, 1
		else:
			nmax[i], nmax[j] = 9 + diff, 9
			nmin[i], nmin[j] = 1, 1 - diff

	nmax = reduce(lambda acc, d: acc * 10 + d, nmax)
	nmin = reduce(lambda acc, d: acc * 10 + d, nmin)
	return nmax, nmin


advent.setup(2021, 24)
fin = advent.get_input()

constraints = get_constraints(fin)
nmax, nmin  = find_max_min(constraints)

advent.print_answer(1, nmax)
advent.print_answer(2, nmin)
