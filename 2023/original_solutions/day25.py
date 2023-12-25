#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 25)
fin = advent.get_input()
lines = read_lines(fin)

g = nx.Graph()

for line in lines:
	a, xb = line.split(': ')
	bs = set(map(str.strip, xb.split()))
	a = a.strip()

	for b in bs:
		g.add_edge(a, b)

victims = nx.minimum_edge_cut(g)

for a, b in victims:
	g.remove_edge(a, b)

answer = prod(map(len, nx.connected_components(g)))

advent.print_answer(1, answer)
