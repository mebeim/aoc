#!/usr/bin/env python3

import utils
from string import ascii_lowercase, ascii_uppercase
from collections import deque

def react_fast(p, ignore=set()):
	l = deque()
	r = deque(p)

	while len(r):
		c = r.popleft()

		if c in ignore:
			continue

		if len(l) and ord(c) ^ ord(l[-1]) == 0x20:
			l.pop()
		else:
			l.append(c)

	return l


utils.setup(2018, 5, dry_run=True)
fin = utils.get_input()

polymer = fin.read().rstrip()
trimmed = ''.join(react_fast(polymer))

reacted_len = len(trimmed)
# assert reacted_len == 9900

utils.submit_answer(1, reacted_len)

best_reacted_len = reacted_len

for l, L in zip(ascii_lowercase, ascii_uppercase):
	reacted_len = len(react_fast(trimmed, {l, L}))

	if reacted_len < best_reacted_len:
		best_reacted_len = reacted_len

# assert best_reacted_len == 4992

utils.submit_answer(2, best_reacted_len)
