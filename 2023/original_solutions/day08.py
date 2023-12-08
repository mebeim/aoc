#!/usr/bin/env python3

from utils.all import *
from itertools import cycle

def steps(G, src, dst, path, p2=False):
	node = src

	for n, d in enumerate(cycle(path), 1):
		if d == 'L':
			node = G[node][0]
		else:
			node = G[node][1]

		if p2 and node[-1] == 'Z':
			break
		elif node == dst:
			break

	return n


advent.setup(2023, 8)
fin = advent.get_input()
lines = read_lines(fin)

G = {}
path = lines[0].strip()
srcs = []
dsts = []

for line in lines[2:]:
	src, a, b = re.findall('\w+', line)
	G[src] = (a, b)

	if src[-1] == 'A': srcs.append(src)
	if a[-1] == 'Z': dsts.append(a)
	if b[-1] == 'Z': dsts.append(b)

ans = steps(G, 'AAA', 'ZZZ', path)
advent.print_answer(1, ans)


ns = []
for src, dst in product(srcs, dsts):
	n = steps(G, src, dst, path, True)
	ns.append(n)

ans = lcm(*ns)

advent.print_and_submit(2, ans)
