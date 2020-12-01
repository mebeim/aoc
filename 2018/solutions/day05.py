#!/usr/bin/env python3

from utils import advent
from string import ascii_lowercase, ascii_uppercase
from collections import deque

def react_fast(p, ignore=set()):
	l = deque()
	r = deque(p)

	while len(r):
		c = r.popleft()

		if c in ignore:
			continue

		if len(l) and c ^ l[-1] == 0x20:
			l.pop()
		else:
			l.append(c)

	return l


advent.setup(2018, 5)
fin = advent.get_input(mode='rb')

polymer = fin.read().rstrip()
trimmed = react_fast(polymer)
reacted_len = len(trimmed)

advent.print_answer(1, reacted_len)


best_reacted_len = reacted_len

for l, L in zip(ascii_lowercase.encode(), ascii_uppercase.encode()):
	reacted_len = len(react_fast(trimmed, {l, L}))

	if reacted_len < best_reacted_len:
		best_reacted_len = reacted_len

advent.print_answer(2, best_reacted_len)
