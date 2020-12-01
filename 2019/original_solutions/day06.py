#!/usr/bin/env python3

from utils.all import *

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

lines = get_lines(fin)
Orbit = namedtuple('Orbit', ['iin', 'out'])
orbits = map(lambda x: Orbit(*x.split(')')), lines)

G = nx.DiGraph()
g = nx.Graph()

for o in orbits:
	G.add_edge(o.out, o.iin)
	g.add_edge(o.out, o.iin)

# eprint(nx.is_connected(G))

tot = 0
seen = set()
leaves = [n for n in G.nodes() if G.in_degree(n)==0 and G.out_degree(n)!=0]
# print(leaves)

# somebody might say this is overkill, unneeded, idiotic... and I would agree
for p in leaves:
	reachable = nx.descendants(G, p)
	# print(p, reachable)

	for other in reachable:
		conn = (p, other)
		if not conn in seen:
			seen.add(conn)
			tot += 1

		reachable2 = nx.descendants(G, other)
		for other2 in reachable2:
			conn = (other, other2)
			if not conn in seen:
				seen.add(conn)
				tot += 1

# print(tot)

advent.submit_answer(1, tot)

# this is also amazingly idiotic
paths_to_santa = nx.all_shortest_paths(g, 'YOU', 'SAN')
best = min(len(p)-3 for p in paths_to_santa)

# 501 wrong
# 500 wrong
# print(best)
advent.submit_answer(2, best)
