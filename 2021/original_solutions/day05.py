#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 5)
if 'debug' not in map(str.lower, sys.argv):
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
0,9 -> 5,9
8,0 -> 0,8
9,4 -> 3,4
2,2 -> 2,1
7,0 -> 7,4
6,4 -> 2,0
0,9 -> 2,9
3,4 -> 1,4
0,0 -> 8,8
5,5 -> 8,2
''')

eprint(*fin, sep='', end='----- end of input -----\n\n'); fin.seek(0, 0)

lol = []
for l in get_lines(fin):
	x, y = l.split('->')
	a, b  = x.split(',')
	c, d  = y.split(',')
	lol.append(tuple(map(int, (a, b, c, d))))

dump_iterable(lol)
sp = defaultdict(int)

for a, b, c, d in lol:
	eprint(a, b, '-', c, d)

	if a == c:
		for y in range(min(b, d), max(b, d) + 1):
			sp[y, a] += 1
	elif b == d:
		for x in range(min(a, c), max(a, c) + 1):
			sp[b, x] += 1

ans = sum(x > 1 for x in sp.values())

advent.print_answer(1, ans)
# wait('Submit? ')
# advent.submit_answer(1, ans)

sp = defaultdict(int)
for a, b, c, d in lol:
	eprint(a, b, '-', c, d)

	if a == c:
		for y in range(min(b, d), max(b, d) + 1):
			sp[y, a] += 1
	elif b == d:
		for x in range(min(a, c), max(a, c) + 1):
			sp[b, x] += 1
	else:
		dx = abs(c - a)
		dy = abs(d - b)

		if dx == dy:

			if c > a and d > b:
				for x, y in zip(range(a, c + 1), range(b, d + 1)):
					sp[y, x] += 1
			if c < a and d > b:
				for x, y in zip(range(a, c - 1, -1), range(b, d + 1)):
					sp[y, x] += 1
			if c > a and d < b:
				for x, y in zip(range(a, c + 1), range(b, d - 1, -1)):
					sp[y, x] += 1
			if c < a and d < b:
				for x, y in zip(range(a, c - 1, -1), range(b, d - 1, -1)):
					sp[y, x] += 1


for x in range(10):
	eprint(x, ':', end='')
	for y in range(10):
		eprint(sp[x, y], end='')
	eprint()

ans = sum(x > 1 for x in sp.values())

advent.print_answer(2, ans)
# wait('Submit? ')
advent.submit_answer(2, ans)
