#!/usr/bin/env python3

from utils import advent
import heapq
from functools import lru_cache
from collections import deque, defaultdict, namedtuple
from itertools import combinations
from math import inf as INFINITY

def neighbors4(grid, r, c):
	for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
		rr, cc = (r + dr, c + dc)

		if 0 <= rr < len(grid) and 0 <= cc < len(grid[rr]):
			if grid[rr][cc] not in '# ':
				yield (rr, cc)

@lru_cache(2**20)
def portal_from_grid(grid, r, c):
	if grid[r][c] != '.':
		return None

	valid = False
	for n1r, n1c in neighbors4(grid, r, c):
		letter1 = grid[n1r][n1c]
		if 'A' <= letter1 <= 'Z':
			valid = True
			break

	if not valid:
		return None

	for n2r, n2c in neighbors4(grid, n1r, n1c):
		letter2 = grid[n2r][n2c]
		if 'A' <= letter2 <= 'Z':
			break

	if n2r > n1r or n2c > n1c:
		key = letter1 + letter2
	else:
		key = letter2 + letter1

	if n2r == 0 or n2c == 0 or n2r == MAXROW or n2c == MAXCOLUMN:
		return Portal(key, 'out', 0)

	return Portal(key, 'in', 0)

@lru_cache(2**20)
def recursive_neighbors(portal):
	depth0_portal    = Portal(portal.label, portal.side, 0)
	depth0_neighbors = G[depth0_portal]
	neighbors = []

	if portal.side == 'in':
		n = Portal(portal.label, 'out', portal.depth + 1)
		neighbors.append((n, 1))

	if portal.depth == 0:
		for n, d in depth0_neighbors:
			if n.side == 'in' or n == ENTRANCE or n == EXIT:
				neighbors.append((n, d))
	else:
		if portal.side == 'out':
			n = Portal(portal.label, 'in', portal.depth - 1)
			neighbors.append((n, 1))

		for n, d in depth0_neighbors:
			if n != ENTRANCE and n != EXIT:
				n = Portal(n.label, n.side, portal.depth)
				neighbors.append((n, d))

	return tuple(neighbors)

def dijkstra(G, src, dst, get_neighbors=None):
	if get_neighbors is None:
		get_neighbors = G.get

	distance = defaultdict(lambda: INFINITY)
	queue    = [(0, src)]
	visited  = set()

	distance[src] = 0

	while queue:
		dist, node = heapq.heappop(queue)

		if node == dst:
			return dist

		if node not in visited:
			visited.add(node)
			neighbors = get_neighbors(node)

			for neighbor, weight in filter(lambda n: n[0] not in visited, neighbors):
				new_dist = dist + weight

				if new_dist < distance[neighbor]:
					distance[neighbor] = new_dist
					heapq.heappush(queue, (new_dist, neighbor))

	return INFINITY

def find_adjacent(grid, src):
	visited = {src}
	queue   = deque()
	found   = []

	for n in neighbors4(grid, *src):
		queue.append((1, n))

	while queue:
		dist, node = queue.popleft()

		if node not in visited:
			visited.add(node)

			portal = portal_from_grid(grid, *node)

			if portal is not None:
				found.append((portal, dist))
				continue

			for neighbor in filter(lambda n: n not in visited, neighbors4(grid, *node)):
				queue.append((dist + 1, neighbor))

	return found

def build_graph(grid):
	graph = {}

	for r, row in enumerate(grid):
		for c in range(len(row)):
			key = portal_from_grid(grid, r, c)

			if key is not None:
				graph[key] = find_adjacent(grid, (r, c))

	return graph

Portal = namedtuple('Portal', ['label', 'side', 'depth'])


advent.setup(2019, 20)
fin = advent.get_input()
grid = tuple(l.strip('\n') for l in fin)

MAXROW    = len(grid) - 1
MAXCOLUMN = len(grid[0]) - 1

G = build_graph(grid)

for p in G:
	if p.label.startswith('AA'):
		ENTRANCE = p
	if p.label.startswith('ZZ'):
		EXIT = p

for p1, p2 in combinations(G, 2):
	if p1.label == p2.label:
		G[p1].append((p2, 1))
		G[p2].append((p1, 1))

min_steps = dijkstra(G, ENTRANCE, EXIT)
advent.print_answer(1, min_steps)


G = build_graph(grid)
min_steps = dijkstra(G, ENTRANCE, EXIT, get_neighbors=recursive_neighbors)
advent.print_answer(2, min_steps)
