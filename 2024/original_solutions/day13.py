#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 13)
fin = advent.get_input()

data = fin.read()
ints = extract_ints(data)


def calc(a, b, prize, pos=Vec(0,0), cost=0, apress=0, bpress=0, cache={}):
	k = (a, b, prize, apress, bpress)
	# print(k)

	if k in cache:
		return cache[k]

	if apress > 100 or bpress > 100:
		cache[k] = False, INFINITY
		return False, INFINITY

	if pos == prize:
		cache[k] = True, cost
		return True, cost

	best = INFINITY

	# Try pressing A
	ok2, res = calc(a, b, prize, pos + a, cost + 3, apress + 1, bpress)
	if ok2 and res < best:
		best = res

	# Try pressing B
	ok1, res = calc(a, b, prize, pos + b, cost + 1, apress, bpress + 1)
	if ok1 and res < best:
		best = res

	res = ((ok1 or ok2), best)
	cache[k] = res
	return res


def smartcalc(a: Vec, b: Vec, prize: Vec):
	s = z3.Optimize()
	apress = z3.Int('apress')
	bpress = z3.Int('bpress')

	s.add(apress > 0)
	s.add(bpress > 0)
	s.add(a.x * apress + b.x * bpress == prize.x)
	s.add(a.y * apress + b.y * bpress == prize.y)
	s.minimize(apress * 3 + bpress)

	if s.check() == z3.sat:
		m = s.model()
		return m.eval(apress).as_long() * 3 + m.eval(bpress).as_long()

	return None


ans1 = ans2 = 0
machines = []

for i in range(0, len(ints), 6):
	ax, ay, bx, by, px, py = ints[i:i+6]
	machines.append((Vec(ax,ay), Vec(bx,by), Vec(px,py)))

# for m in machines:
# 	print(m)

for m in machines:
	ok, c = calc(*m)
	print(m, '->', ok, c)
	if ok:
		ans1 += c

advent.print_answer(1, ans1)


for m in machines:
	a, b, p = m
	p += (10000000000000, 10000000000000)
	res = smartcalc(a, b, p)
	if res is not None:
		ans2 += res

advent.print_answer(2, ans2)
