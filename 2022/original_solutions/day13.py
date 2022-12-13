#!/usr/bin/env python3

from itertools import zip_longest
from functools import cmp_to_key

from utils.all import *

def check_pair(la, lb, debug=False, depth=0):
	log = rlog(depth)
	if debug: log(f'> {la} {lb}\n')

	if type(la) is int and type(lb) is int:
		if la < lb:
			if debug: log('1\n')
			return 1
		if la == lb:
			if debug: log('IDK\n')
			return 0
		if debug: log('-1\n')
		return -1

	if type(la) is list and type(lb) is list:
		for a, b in zip_longest(la, lb):
			if a is None:
				if debug: log('1\n')
				return 1
			if b is None:
				if debug: log('-1\n')
				return -1

			res = check_pair(a, b, debug, depth+1)
			if res == 0:
				continue

			if debug: log(f'{res}\n')
			return res

		if debug: log('1\n')
		return 0

	if type(la) is int:
		res = check_pair([la], lb, debug, depth+1)
		if debug: log(f'{res}\n')
		return res

	if type(lb) is int:
		res = check_pair(la, [lb], debug, depth+1)
		if debug: log(f'{res}\n')
		return res

	assert False


advent.setup(2022, 13)
fin = advent.get_input()

ans = 0
data = fin.read()
lines = data.strip().split('\n\n')
groups = [l.split('\n') for l in lines]

for g in groups:
	# Dumb eval sanity check
	assert set(g[0] + g[1]).issubset(set('[]0123456789,'))

	g[0] = eval(g[0])
	g[1] = eval(g[1])

for i, (la, lb) in enumerate(groups, 1):
	res = check_pair(la, lb)
	# print(i, res, la, lb)
	if res > 0:
		ans += i

# 6506 wrong
advent.print_answer(1, ans)


pkts = []
for g in groups:
	pkts.extend(g)

pkts.append([[2]])
pkts.append([[6]])

pkts.sort(key=cmp_to_key(check_pair), reverse=True)

ans = 1
for i, p in enumerate(pkts, 1):
	if p == [[2]] or p == [[6]]:
		ans *= i

advent.print_answer(2, ans)
