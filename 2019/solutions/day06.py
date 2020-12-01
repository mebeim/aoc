#!/usr/bin/env python3

from utils import advent
import heapq
from collections import defaultdict

def count_orbits(planet):
	total = 0
	while planet in T:
		total += 1
		planet = T[planet]

	return total

def dijkstra(G, src, dst):
	queue = [(0, src)]
	visited = set()
	distance = defaultdict(lambda: float('inf'))
	distance[src] = 0

	while queue:
		dist, planet = heapq.heappop(queue)

		if planet == dst:
			return dist

		if planet not in visited:
			visited.add(planet)

			for neighbor in filter(lambda p: p not in visited, G[planet]):
				new_dist = dist + 1

				if new_dist < distance[neighbor]:
					distance[neighbor] = new_dist
					heapq.heappush(queue, (new_dist, neighbor))

	return float('inf')


advent.setup(2019, 6)
fin = advent.get_input()

orbits = tuple(map(lambda l: l.strip().split(')'), fin.readlines()))

T = {child: parent for parent, child in orbits}
n_orbits = sum(map(count_orbits, T))
advent.print_answer(1, n_orbits)


G = defaultdict(set)

for a, b in orbits:
	G[a].add(b)
	G[b].add(a)

min_transfers = dijkstra(G, T['YOU'], T['SAN'])
advent.print_answer(2, min_transfers)

# Using networkx:
# G = nx.DiGraph(orbits)
# n_orbits = sum(len(nx.descendants(G, n)) for n in G)
# min_transfers = len(nx.shortest_path(G.to_undirected(), 'YOU', 'SAN')) - 3
