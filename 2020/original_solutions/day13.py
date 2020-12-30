#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 13)
fin = advent.get_input()

# fin = io.StringIO('''\
# 939
# 7,13,x,x,59,x,31,19
# ''')

# eprint(*fin, sep=''); fin.seek(0, 0)
timer_start()

target = int(fin.readline())
raw = fin.readline().strip().split(',')
times = filter(lambda x: x != 'x', raw)
times = list(map(int, times))

best = 99999999999999999
ans = -1
for t in times:
	if target % t == 0:
		mul = target // t
	else:
		mul = target // t + 1

	delta = mul * t - target
	# eprint(t, best, delta)

	if delta < best:
		best = delta
		ans = t * delta

advent.print_answer(1, ans)


# Google search "python chinese remainder theorem"
from functools import reduce
def chinese_remainder(n, a):
	ssum = 0
	prod = reduce(lambda a, b: a*b, n)
	for n_i, a_i in zip(n, a):
		p = prod // n_i
		ssum += a_i * pow(p, -1, n_i) * p
	return ssum % prod

buses = []
for i, t in enumerate(raw):
	if t != 'x':
		buses.append((i, int(t)))

_n = []
_a = []

for a, n in buses:
	a = a % n
	a = (n-a) % n
	# eprint('t ===', a, 'mod', n)

	_n.append(n)
	_a.append(a)

t = chinese_remainder(_n, _a)
advent.print_answer(2, t)
