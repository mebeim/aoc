#!/usr/bin/env python3

from utils.all import *

def emu(flow, x, m, a, s):
	cur = 'in'

	while cur != 'A' and cur != 'R':
		insns, last = flow[cur]

		for exp, nxt in insns:
			if eval(exp):
				cur = nxt
				break
		else:
			cur = last

	if cur == 'A':
		return x + m + a + s
	return 0

# @log_calls_recursive()
def emu_comb(cur='in', vars={'x': (1,4000), 'm': (1,4000), 'a': (1,4000), 's': (1,4000)}):
	if cur == 'R':
		return 0

	if cur == 'A':
		x = [mmax - mmin + 1 for mmin, mmax in vars.values()]
		# emu_comb.eprint(x)
		return prod(x)

	for (mmin, mmax) in vars.values():
		assert mmin <= mmax

	insns, last = flow[cur]
	total = 0

	for exp, nxt in insns:
		var, op, value = exp[0], exp[1], exp[2:]
		value = int(value)

		if op == '<':
			mmin, mmax = vars[var]
			if mmin < value:
				newvars = vars | {var: (mmin, value - 1)}
				total += emu_comb(nxt, newvars)

			# to advance satisfy the opposite (>=)
			if mmax >= value:
				vars[var] = (value, mmax)
			else:
				break
		else:
			mmin, mmax = vars[var]
			if mmax > value:
				newvars = vars | {var: (value + 1, mmax)}
				total += emu_comb(nxt, newvars)

			# to advance satisfy the opposite (<=)
			if mmin <= value:
				vars[var] = (mmin, value)
			else:
				break

	total += emu_comb(last, deepcopy(vars))
	return total


advent.setup(2023, 19)
fin = advent.get_input()
data = fin.read()

ans1 = ans2 = 0
progs, vals = data.split('\n\n')
progs = progs.splitlines()
vals = vals.splitlines()

flow = {}

for p in progs:
	name = re.findall(r'(\w+)\{.+', p)[0]
	insns = p[p.find('{') + 1:-1]
	insns = insns.split(',')
	insns = list(map(lambda x: tuple(x.split(':')), insns))
	last = insns.pop()[0]

	flow[name] = (insns, last)

for v in vals:
	x, m, a, s = extract_ints(v)
	ans1 += emu(flow, x, m, a, s)

advent.print_answer(1, ans1)

ans2 = emu_comb()
advent.print_answer(2, ans2)
