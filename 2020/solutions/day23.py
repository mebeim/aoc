#!/usr/bin/env python3

from utils import advent

def build_list(cups, n=None):
	initial_sz = max(cups) + 1
	next_cup   = [0] * initial_sz

	for prev, cur in zip(cups, cups[1:]):
		next_cup[prev] = cur

	if n is None:
		next_cup[cups[-1]] = cups[0]
	else:
		next_cup += list(range(initial_sz + 1, n + 2))
		next_cup[n] = cups[0]
		next_cup[cups[-1]] = initial_sz

	return next_cup

def play(cur, next_cup, n_rounds):
	max_cup = len(next_cup) - 1

	for _ in range(n_rounds):
		first  = next_cup[cur]
		mid    = next_cup[first]
		last   = next_cup[mid]
		picked = (first, mid, last)

		next_cup[cur] = next_cup[last]

		dst = max_cup if cur == 1 else cur - 1
		while dst in picked:
			dst = max_cup if dst == 1 else dst - 1

		next_cup[last] = next_cup[dst]
		next_cup[dst]  = first
		cur = next_cup[cur]


advent.setup(2020, 23)

fin = advent.get_input()
orig = tuple(map(int, fin.readline().rstrip()))

next_cup = build_list(orig)
play(orig[0], next_cup, 100)

ans = ''
cur = next_cup[1]
while cur != 1:
	ans += str(cur)
	cur = next_cup[cur]

advent.print_answer(1, ans)


next_cup = build_list(orig, 1000000)
play(orig[0], next_cup, 10000000)
ans = next_cup[1] * next_cup[next_cup[1]]

advent.print_answer(2, ans)
