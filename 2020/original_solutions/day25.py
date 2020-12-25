#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 25)
fin = advent.get_input()
timer_start()

pub1, pub2 = map(int, fin)

from math import ceil, sqrt

def bsgs(g, h, p):
	# https://gist.github.com/0xTowel/b4e7233fc86d8bb49698e4f1318a5a73
	N = ceil(sqrt(p - 1))
	tbl = {pow(g, i, p): i for i in range(N)}
	c = pow(g, N * (p - 2), p)

	for j in range(N):
		y = (h * pow(c, j, p)) % p
		if y in tbl:
			return j * N + tbl[y]

loop_sz = bsgs(7, pub1, 20201227)
ans = pow(pub2, loop_sz, 20201227)

advent.print_answer(1, ans)
