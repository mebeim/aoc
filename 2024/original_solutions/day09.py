#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 9)
fin = advent.get_input()

data = fin.read()
ans1 = ans2 = 0
fs = list(map(int, data.strip()))

ls = []

for i, f in enumerate(fs):
	if i % 2 == 0:
		fid = i // 2
		ls.extend([fid] * f)
	else:
		ls.extend([-1] * f)

LEN = len(ls)
r = LEN - 1
l = 0

while 1:
	# find first hole
	while l < LEN and ls[l] != -1:
		l += 1

	# find first non-hole from right
	while r >= 0 and ls[r] == -1:
		r -= 1

	if l >= r:
		break

	# swap
	ls[l] = ls[r]
	ls[r] = -1

for i, x in enumerate(ls):
	if x == -1:
		break
	ans1 += i * x

advent.print_answer(1, ans1)


q = []
i = 0
prev = None
previ = 0

while i < LEN:
	x = ls[i]
	if x == prev:
		i += 1
		continue

	if prev is not None:
		q.append((prev, previ, i - previ))

	prev = x
	previ = i
	i += 1

q.append((prev, previ, i - previ))

prio = deque(sorted(filter(lambda x: x[0] != -1, q), reverse=True))
holes = deque(map(itemgetter(1, 2), filter(lambda x: x[0] == -1, q)))
offset = 0

# eprint(prio)

while prio:
	bid, boff, bsz = prio.popleft()
	# eprint('placing', bid, boff, bsz)
	# eprint('holes', holes)

	# find first hole from left that fits the block
	fit = False
	for hi, hole in enumerate(holes):
		hoff, hsz = hole
		if hoff < boff and hsz >= bsz:
			break
	else:
		# does not fit, stays where it is
		# eprint('>', bid, boff, bsz)
		ans2 += sum(i * bid for i in range(boff, boff + bsz))
		continue


	# eprint('fits', *hole)

	if hsz > bsz:
		# shrink hole
		holes[hi] = (hoff + bsz, hsz - bsz)
	else:
		# fill hole
		holes.remove(hole)

	# eprint('>', bid, hoff, bsz)
	ans2 += sum(i * bid for i in range(hoff, hoff + bsz))

advent.print_answer(2, ans2)
