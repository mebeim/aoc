#!/usr/bin/env python3

from utils import advent

advent.setup(2018, 1)

done = False
ans = sum(map(int, advent.get_input()))

advent.submit_answer(1, ans)

seen = set()
seen.add(0)
ans = 0

while not done:
	for d in advent.get_input():
		ans += int(d)

		if ans in seen:
			ans2 = ans
			done = True
			break

		seen.add(ans)

advent.submit_answer(2, ans2)
