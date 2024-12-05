#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 5)
fin = advent.get_input()

data = fin.read()
ans1 = ans2 = 0


def check(g, nodes):
	idx = dict((x, i) for i, x in enumerate(nodes))

	for x in nodes:
		for nxt in g[x]:
			if nxt in idx and idx[nxt] < idx[x]:
				return False

	return True


def middle(g, nodes):
	last = None
	seen = set()
	nodes = set(nodes)

	for _ in range(len(nodes) // 2 + 1):
		for x in nodes:
			for other in nodes:
				if other == x:
					continue

				# if other should come before x it's wrong
				if x in g[other]:
					break
			else:
				last = x
				seen.add(x)
				nodes.remove(x)
				break

	assert last is not None
	return last


sec = data.split('\n\n')
g = defaultdict(set)

for line in sec[0].splitlines():
	a, b = map(int, line.split('|'))
	g[a].add(b)

# dump_dict(g)
good_lines = set()

for i, line in enumerate(sec[1].splitlines()):
	lst = list(map(int, line.split(',')))

	if check(g, lst):
		assert len(lst) % 2 == 1
		ans1 += lst[len(lst) // 2]
		good_lines.add(i)

# 10683 wrong
advent.print_answer(1, ans1)


for i, line in enumerate(sec[1].splitlines()):
	if i in good_lines:
		continue

	nodes = list(map(int, line.split(',')))
	ans2 += middle(g, nodes)

advent.print_answer(2, ans2)
