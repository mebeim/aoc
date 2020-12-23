#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 23)
timer_start()

orig = list(map(int, '523764819'))

if 'test' in sys.argv:
	orig = list(map(int, '389125467'))

cups = deque(orig)
mincup, maxcup = min(cups), max(cups)

for move in range(100):
	cur = cups[0]

	cups.rotate(-1)
	picked = [cups.popleft() for _ in range(3)]

	dst = cur - 1
	while dst in picked or dst > maxcup or dst < mincup:
		dst -= 1
		if dst < mincup:
			dst = maxcup

	dsti = cups.index(dst)

	cups.rotate(-dsti - 1)
	cups.extendleft(picked[::-1])
	cups.rotate(dsti + 1)

cups.rotate(1)
i = cups.index(1)
cups.rotate(-i)
cups.popleft()

ans = ''.join(map(str, cups))
advent.print_answer(1, ans)


class Cup:
	__slots__ = ('v', 'l', 'r')
	def __init__(self, v):
		self.v = v
		self.l = None
		self.r = None

	def __repr__(self):
		v, l, r = self.v, self.l, self.r
		return f'<{l.v} ({v}) {r.v}>'

def play(first_cup, valmap, moves):
	cur = first_cup
	mincup, maxcup = 1, len(cups)

	for move in range(moves):
		# if move % 500000 == 0:
		# 	eprint('Move', move)

		# tmp = cur
		# eprint(move + 1)
		# for _ in range(len(cups)):
		# 	eprint(tmp, end=' ')
		# 	tmp = tmp.r
		# eprint()

		first_pick, mid, last_pick = cur.r, cur.r.r, cur.r.r.r

		picked = (first_pick, mid, last_pick)
		picked_vals = tuple(map(attrgetter('v'), picked))

		cur.r = last_pick.r
		cur.r.l = cur

		dst = cur.v - 1
		while dst in picked_vals or dst > maxcup or dst < mincup:
			dst -= 1
			if dst < mincup:
				dst = maxcup

		# eprint(' ', *picked)
		dst = valmap[dst]
		last_pick.r = dst.r
		last_pick.r.l = last_pick
		dst.r = first_pick
		first_pick.l = dst
		# eprint(' ', *picked)
		cur = cur.r

	# p1 sanity check
	# res = ''
	# c1 = valmap[1]
	# c = c1.r
	# while c != c1:
	# 	res += str(c.v)
	# 	c = c.r

	c1 = valmap[1]
	return c1.r.v * c1.r.r.v

from itertools import chain
lst = chain(iter(orig), range(10, 1000000 + 1))

cups = list(map(Cup, lst))
cups[0].l = cups[-1]
cups[-1].r = cups[0]

for i in range(len(cups) - 1):
	cups[i].r = cups[i + 1]
	cups[i + 1].l = cups[i]

valmap = [None] * (len(cups) + 1)
for c in cups:
	valmap[c.v] = c

p2 = play(cups[0], valmap, 10000000)
advent.print_answer(2, p2)
