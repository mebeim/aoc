#!/usr/bin/env python3

import advent
import networkx as nx

advent.setup(2019, 6, dry_run=True)
fin = advent.get_input()

orbits = tuple(map(lambda l: l.strip().split(')'), fin.readlines()))

G = nx.DiGraph(orbits)
n_orbits = sum(len(nx.descendants(G, n)) for n in G)

assert n_orbits == 253104
advent.submit_answer(1, n_orbits)

G = G.to_undirected()
transfers = len(nx.shortest_path(G, 'YOU', 'SAN')) - 3

assert transfers == 499
advent.submit_answer(2, transfers)
