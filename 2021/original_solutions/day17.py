#!/usr/bin/env python3

from utils.all import *

xmin, xmax = 282, 314
ymin, ymax = -80, -45

def f(vx, vy):
	x, y = 0,0
	best = -INFINITY

	while 1:
		if y < ymin:
			return None

		if ymin <= y <= ymax:
			if xmin <= x <= xmax:
				return best

		if y > best:
			best = y

		x += vx
		y += vy

		if vx > 0:
			vx -= 1
		elif vx < 0:
			vx += 1

		vy -= 1

	return -INFINITY

best = -INFINITY
cool = set()

# PyPy bruteforce FTW
for vx in range(-1500, 1500):
	# eprint(vx, best, len(cool))

	for vy in range(-1500, 1500):
		v = f(vx, vy)
		if v is None:
			continue
		else:
			cool.add((vx, vy))
		if v > best:
			best = v

ans = best

advent.print_answer(1, ans)
# wait('Submit? ')
# advent.submit_answer(1, ans)

ans = len(cool)

advent.print_answer(2, ans)
# wait('Submit? ')
# advent.submit_answer(2, ans)
