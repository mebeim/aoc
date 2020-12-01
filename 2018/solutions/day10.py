#!/usr/bin/env python3

from utils import advent
import re

def simulate(pts, t):
	xs = [x + t*v for x,_,v,_ in pts]
	ys = [y + t*v for _,y,_,v in pts]
	return tuple(zip(xs, ys))

def box(pts):
	minx, maxx = min(p[0] for p in pts), max(p[0] for p in pts)
	miny, maxy = min(p[1] for p in pts), max(p[1] for p in pts)
	return minx, miny, maxx-minx, maxy-miny

def search(pts):
	t1 = 0
	t2 = 1
	f1 = box(simulate(pts, t1))[3]

	while f1 > box(simulate(pts, t2))[3]:
		t2 <<= 1

	while t1 != t2:
		t = (t1 + t2)//2
		m = box(simulate(pts, t    ))[3]
		r = box(simulate(pts, t + 1))[3]

		if r > m:
			t2 = t
		else:
			t1 = t+1

	return t1

advent.setup(2018, 10)
fin = advent.get_input()

points = []
for line in fin:
	points.append(tuple(map(int, re.findall(r'-?\d+', line))))

t = search(points)

final_points = set(simulate(points, t))
x, y, w, h = box(final_points)

word = ''
for j in range(y, y + h + 1):
	for i in range(x, x + w + 1):
		word += '#' if (i, j) in final_points else ' '
	word += '\n'

# Can't really print this nicely, but whatever
advent.print_answer(1, '\n' + word)
advent.print_answer(2, t)
