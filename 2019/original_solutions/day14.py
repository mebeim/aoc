#!/usr/bin/env python3

from utils.all import *

advent.setup(2019, 14)
fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

lines = get_lines(fin)

produced = {}
needed = {}
left = defaultdict(int)

for l in lines:
	a, b = l.split(' => ')
	aa = a.split(', ')

	b = b.split()
	b_num, b_name = int(b[0]), b[1]

	produced[b_name] = b_num
	needed[b_name] = {}

	for el in aa:
		x = el.split()
		a_num, a_name = int(x[0]), x[1]

		needed[b_name][a_name] = a_num
		left[a_name] += 1


from copy import deepcopy

def solve(wanted_fuel):
	global left

	want = defaultdict(int)
	want['FUEL'] = wanted_fuel

	_left = deepcopy(left)
	_left['FUEL'] = 0

	while 1:
		goal = min(_left, key=_left.get)
		assert _left[goal] == 0
		del _left[goal]

		if goal == 'ORE':
			ans = want[goal]
			break

		wanted_qty = want[goal]
		recipe_qty = produced[goal]
		multiplier = wanted_qty // recipe_qty

		if wanted_qty % recipe_qty != 0:
			multiplier += 1

		for req, nreq in needed[goal].items():
			want[req] += nreq * multiplier
			_left[req] -= 1

	return ans


# print(solve(1))
ans = solve(1)
advent.submit_answer(1, ans)

# hehe, good ol' manual binary search
n = int(sys.argv[1])
s = solve(n)
print(s, 'delta', 1000000000000 - s)

# advent.submit_answer(2, ans2)
