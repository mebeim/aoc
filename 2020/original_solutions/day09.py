#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 9)
fin = advent.get_input()
timer_start()

ints = get_ints(fin, True)

for k in range(25, len(ints)):
	ok = False
	c = ints[k]

	for i in range(k - 25, k):
		for j in range(k - 25, k):
			if i == j:
				continue
			a, b = ints[i], ints[j]

			if a + b == c:
				ok = True
				break

		if ok:
			break

	if not ok:
		ans = c
		break

advent.submit_answer(1, ans)

c = 32321523
for i in range(len(ints)):
	for j in range(i + 1, len(ints)):
		if sum(ints[i:j]) == c:
			M = max(ints[i:j])
			m = min(ints[i:j])
			ans2 = m + M

			advent.submit_answer(2, ans2)
			sys.exit(0)
