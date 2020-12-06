#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 6)
fin = advent.get_input()
eprint(*fin, sep=''); fin.seek(0, 0)
timer_start()

data = fin.read().split('\n\n')

ans = 0
ans2 = 0
for el in data:
	ans += len(set(el.replace('\n', '')))

	el = el.splitlines()
	ally = set(el[0])
	for l in el[1:]:
		ally &= set(l)

	ans2 += len(ally)

advent.submit_answer(1, ans)
advent.submit_answer(2, ans2)
