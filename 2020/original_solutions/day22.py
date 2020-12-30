#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 22)
fin = advent.get_input()
TESTPLZ = any(a.lower() == 'test' for a in sys.argv[1:])
ftest = io.StringIO('''\
Player 1:
9
2
6
3
1

Player 2:
5
8
4
7
10
''')

if TESTPLZ:
	fin = ftest

# eprint(*fin, sep=''); fin.seek(0, 0)
timer_start()

p1, p2 = fin.read().split('\n\n')
p1 = p1.splitlines()
p2 = p2.splitlines()

orig1 = list(map(int, p1[1:]))
orig2 = list(map(int, p2[1:]))

p1 = deque(orig1)
p2 = deque(orig2)
# i = 1

while p1 and p2:
	# eprint(i)
	# eprint(p1)
	# eprint(p2)
	# eprint('---'*10)

	c1, c2 = p1.popleft(), p2.popleft()

	if c1 > c2:
		p1.append(c1)
		p1.append(c2)
	elif c2 > c1:
		p2.append(c2)
		p2.append(c1)
	else:
		assert False, 'wtf'

	# i += 1

w = p1 if p1 else p2
w = list(w)

n = 1
ans = 0
for c in w[::-1]:
	ans += n * c
	n += 1

advent.print_answer(1, ans)


def play(p1, p2, gameno=1):
	memory = set()
	# rnd = 1

	while p1 and p2:
		# eprint('game', gameno, 'round', rnd)
		# eprint(p1)
		# eprint(p2)
		# eprint('---'*10)

		k = (tuple(p1), tuple(p2))
		if k in memory:
			return 1, p1
		memory.add(k)

		c1, c2 = p1.popleft(), p2.popleft()

		if c1 <= len(p1) and c2 <= len(p2):
			l1, l2 = list(p1), list(p2)
			l1, l2 = deque(l1[:c1]), deque(l2[:c2])
			winner, _ = play(l1, l2, gameno + 1)
		else:
			if c1 > c2:
				winner = 1
			else:
				winner = 2

		if winner == 1:
			p1.append(c1)
			p1.append(c2)
		else:
			p2.append(c2)
			p2.append(c1)

		# rnd += 1

	w = p1 if p1 else p2
	w = list(w)

	return 1 if p1 else 2, w

p1 = deque(orig1)
p2 = deque(orig2)

p, w = play(p1, p2)
w = list(w)

n = 1
ans2 = 0
for c in w[::-1]:
	ans2 += n * c
	n += 1

# 32448 wrong
# 33880 wrong
advent.print_answer(2, ans2)
