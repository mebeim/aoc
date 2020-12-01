#!/usr/bin/env python3

from utils.all import *
import z3

advent.setup(2018, 23)
fin = advent.get_input()
# print(*fin)
timer_start()

##################################################

intmat = get_int_matrix(fin, True)
bots = []

for l in intmat:
	x, y, z, r = l
	bots.append((r, x, y, z))

timer_start('Part 1')

best = max(bots)
br, bx, by, bz = best
tot = 0

for b in bots:
	r, x, y, z = b
	if abs(x-bx)+abs(y-by)+abs(z-bz) <= br:
		tot += 1

advent.submit_answer(1, tot)
timer_stop('Part 1')


timer_start('Part 2')

def dist1d(a, b):
	d = a - b
	return z3.If(d >= 0, d, -d)

def manhattan(ax, ay, az, bx, by, bz):
	return dist1d(ax, bx) + dist1d(ay, by) + dist1d(az, bz)

solver = z3.Optimize()

bestx = z3.Int('bestx')
besty = z3.Int('besty')
bestz = z3.Int('bestz')
distance = z3.Int('distance')

inside = []
for i, b in enumerate(bots):
	br, *bxyz = b
	bot = z3.Int('b{:4d}'.format(i))
	ok = z3.If(manhattan(bestx, besty, bestz, *bxyz) <= br, 1, 0)
	solver.add(bot == ok)
	inside.append(bot)

solver.add(distance == manhattan(bestx, besty, bestz, 0, 0, 0))

solver.maximize(z3.Sum(*inside))
solver.minimize(distance)

solver.check()

m = solver.model()
min_distance = m.eval(distance)

# best = ','.join(map(str, (m.eval(bestx), m.eval(besty), m.eval(bestz))))
# print(best)


# 124672786,46423329,60063431 not right
# -112484866,-122420778,-123350868 not right
# 56871640,47545783,53290655 not right
advent.submit_answer(2, min_distance)
timer_stop('Part 2')
