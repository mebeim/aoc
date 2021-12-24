#!/usr/bin/env python3

import z3

def add_constraints(s, inp):
	for digit in inp:
		s.add(digit > 0)
		s.add(digit < 10)

	v5 = inp[1]
	v6 = (inp[0] + 4) * (inp[0] != 12) % 26 + 15 != v5
	v7 = (v5 + 11) * v6 + (25 * v6 + 1) * (inp[0] + 4) * (inp[0] != 12)
	v8 = (inp[2] + 7) * (v7 % 26 + 11 != inp[2]) + (25 * (v7 % 26 + 11 != inp[2]) + 1) * v7
	v9 = (inp[3] + 2) * (v8 % 26 - 14 != inp[3]) + v8 / 26 * (25 * (v8 % 26 - 14 != inp[3]) + 1)
	v10 = (inp[4] + 11) * (v9 % 26 + 12 != inp[4]) + v9 * (25 * (v9 % 26 + 12 != inp[4]) + 1)
	v11 = (inp[5] + 13) * (v10 % 26 - 10 != inp[5]) + v10 / 26 * (25 * (v10 % 26 - 10 != inp[5]) + 1)
	v12 = (inp[6] + 9) * (v11 % 26 + 11 != inp[6]) + (25 * (v11 % 26 + 11 != inp[6]) + 1) * v11
	v13 = (inp[7] + 12) * (v12 % 26 + 13 != inp[7]) + (25 * (v12 % 26 + 13 != inp[7]) + 1) * v12
	v14 = (inp[8] + 6) * (v13 % 26 - 7 != inp[8]) + v13 / 26 * (25 * (v13 % 26 - 7 != inp[8]) + 1)
	v15 = (inp[9] + 2) * (v14 % 26 + 10 != inp[9]) + v14 * (25 * (v14 % 26 + 10 != inp[9]) + 1)
	v16 = (inp[10] + 11) * (v15 % 26 - 2 != inp[10]) + v15 / 26 * (25 * (v15 % 26 - 2 != inp[10]) + 1)
	v17 = (inp[11] + 12) * (v16 % 26 - 1 != inp[11]) + v16 / 26 * (25 * (v16 % 26 - 1 != inp[11]) + 1)
	v18 = (inp[12] + 3) * (v17 % 26 - 4 != inp[12]) + v17 / 26 * (25 * (v17 % 26 - 4 != inp[12]) + 1)
	res = (inp[13] + 13) * (v18 % 26 - 12 != inp[13]) + v18 / 26 * (25 * (v18 % 26 - 12 != inp[13]) + 1)

	tot = 0
	for digit in inp:
		tot = tot * 10 + digit

	s.add(res == 0)
	return tot

def solve(inp, maximize=True):
	s = z3.Optimize()
	value = add_constraints(s, inp)

	if maximize:
		s.maximize(value)
	else:
		s.minimize(value)

	assert s.check() == z3.sat

	m = s.model()
	return m.eval(value)


inp = [z3.Int('x{}'.format(i)) for i in range(14)]

print('Part 1:', solve(inp, maximize=True))
print('Part 2:', solve(inp, maximize=False))
