#!/usr/bin/env python3

from utils.all import *

class X:
	def __init__(self, v):
		self.v = int(v)
		self.prev = None
		self.next = None

	def __repr__(self):
		return f'([{self.prev.v:12d}]<-[{self.v:12d}]->[{self.next.v:12d}])'

def unlink(x):
	x.prev.next = x.next
	x.next.prev = x.prev

def link(x, prv, nxt):
	x.prev = prv
	x.next = nxt
	prv.next = nxt.prev = x

# Good lord have mercy
def move(x, n):
	# eprint('move', x, 'steps', x.v % n)

	if x.v >= 0:
		if abs(x.v) < n:
			if x.v % n == 0:
				return

			unlink(x)

			prev = x
			for _ in range(x.v % n):
				prev = prev.next

			nxt = prev.next
		else:
			# eprint('actually', x.v % (n - 1))
			if x.v % (n - 1) == 0:
				return

			unlink(x)

			prev = x
			for _ in range(x.v % (n - 1)):
				prev = prev.next

			nxt = prev.next
	else:
		if abs(x.v) < n:
			unlink(x)

			nxt = x
			for _ in range(x.v % n):
				nxt = nxt.next

			prev = nxt.prev
		else:
			# eprint('actually', x.v % (n - 1))
			if x.v % (n - 1) == 0:
				return

			unlink(x)

			prev = x
			for _ in range(x.v % (n - 1)):
				prev = prev.next

	link(x, prev, prev.next)
	# eprint(prev, x, nxt)

def sol(cur):
	for _ in range(1000):
		cur = cur.next
	# eprint(cur.v)
	yield cur.v

	for _ in range(1000):
		cur = cur.next
	# eprint(cur.v)
	yield cur.v

	for _ in range(1000):
		cur = cur.next
	# eprint(cur.v)
	yield cur.v

def dump(start):
	cur = start
	while 1:
		# eprint(cur.v, end=' ')
		cur = cur.next
		if cur is start:
			break
	# eprint()


advent.setup(2022, 20)
fin = advent.get_input() if 'debug' not in sys.argv else io.StringIO('''\
1
2
-3
3
-2
0
4
''')

ints = tuple(map(int, fin))
l = tuple(map(X, ints))
n = len(l)

for i, x in enumerate(l):
	x.prev = l[(i - 1) % n]
	x.next = l[(i + 1) % n]

dump(l[0])

for x in l:
	move(x, n)
	dump(l[0])

zero = None
for x in l:
	if x.v == 0:
		zero = x
		break

ans = sum(sol(zero))
advent.print_answer(1, ans)


l = tuple(map(lambda v: X(v * 811589153), ints))

for i, x in enumerate(l):
	x.prev = l[(i - 1) % n]
	x.next = l[(i + 1) % n]

dump(l[0])

for i in range(10):
	for x in l:
		move(x, n)
		dump(l[0])

	# eprint('-' * 50)
	# eprint(i + 1, end=': ')
	# dump(l[0])

zero = None
for x in l:
	if x.v == 0:
		zero = x
		break

ans = sum(sol(zero))
advent.print_answer(2, ans)
