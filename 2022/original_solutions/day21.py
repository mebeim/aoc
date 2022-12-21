#!/usr/bin/env python3

import z3
from operator import add, sub, mul, floordiv

from utils.all import *

def calc(vals, left, right):
	vals = deepcopy(vals)

	var = z3.BitVec('humn', 64)
	vals['humn'] = var

	s = z3.Optimize()
	s.add(var > 0)

	for x in order:
		if x in g:
			a, b = g[x]
			op = ops[x]

			if op == '/' and (type(vals[a]) is not int or type(vals[b]) is not int):
				vals[x] = vals[a] / vals[b]
			else:
				vals[x] = opmap[op](vals[a], vals[b])

	s.add(vals[left] == vals[right])
	s.minimize(var)

	assert s.check() == z3.sat
	m = s.model()
	return m.eval(var).as_long()


advent.setup(2022, 21)
fin = advent.get_input()

ans = 0
g = defaultdict(list)
vals = {}
ops  = {}

for line in fin:
	a, b = line.strip().split(': ')

	if b.isdigit():
		vals[a] = int(b)
	else:
		l, op, r = b.split()
		g[a].append(l)
		g[a].append(r)
		ops[a] = op

original_vals = deepcopy(vals)

order = toposort(g, reverse=True)
opmap = {
	'*': mul,
	'+': add,
	'-': sub,
	'/': floordiv
}

for x in order:
	if x in g:
		a, b = g[x]
		op = ops[x]
		vals[x] = opmap[op](vals[a], vals[b])
		# eprint(x, a, b)

ans = vals['root']

advent.print_answer(1, ans)


left, right = g['root']
ans = calc(original_vals, left, right)

# 3408640841017497240 wrong
advent.print_answer(2, ans)
