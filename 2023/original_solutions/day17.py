#!/usr/bin/env python3

from utils.all import *

def calc_direction(ra, ca, rb, cb):
	return rb - ra, cb - ca

def turning_around(dra, dca, drb, dcb):
	if dra and drb and dra + drb == 0:
		return True
	if dca and dcb and dca + dcb == 0:
		return True
	return False

def get_neighbors_plz(r, c, cur_direction, noturn_dist):
	for (nr, nc), w in g[r,c]:
		new_direction = calc_direction(r, c, nr, nc)

		if new_direction == cur_direction:
			yield (nr, nc), w, new_direction, noturn_dist + 1
		else:
			yield (nr, nc), w, new_direction, 1


def dijkstra(g, src, dst, p2=False):
	distance = defaultdict(lambda: INFINITY, {src: 0})
	queue    = []
	visited  = set()

	for (nr, nc), w in g[src]:
		queue.append((w, 1, calc_direction(*src, nr, nc), (nr, nc)))

	heapq.heapify(queue)

	while queue:
		dist, noturn_dist, direction, node = heapq.heappop(queue)

		if node == dst:
			return dist

		k = (node, direction, noturn_dist)
		if k in visited:
			continue

		visited.add(k)
		neighbors = get_neighbors_plz(*node, direction, noturn_dist)
		neighbors = list(neighbors)

		if not neighbors:
			continue

		for neighbor, weight, new_direction, new_noturn_dist in filter(lambda n: n[0] not in visited, neighbors):
			if not p2:
				if new_noturn_dist > 3:
					continue
			else:
				if not (new_noturn_dist <= 10 and (new_direction == direction or noturn_dist >= 4)):
					continue

			if turning_around(*direction, *new_direction):
				continue

			new_dist = dist + weight
			k = (neighbor, new_direction, new_noturn_dist)

			if new_dist < distance[k]:
				distance[k] = new_dist
				heapq.heappush(queue, (new_dist, new_noturn_dist, new_direction, neighbor))

	return INFINITY


advent.setup(2023, 17)
fin = advent.get_input()
grid = read_char_matrix(fin)

g = defaultdict(list)

for r, row in enumerate(grid):
	for c, char in enumerate(row):
		for nr, nc in neighbors4(grid, r, c):
			g[r,c].append(((nr, nc), int(grid[nr][nc])))

w, h = len(grid[0]), len(grid)

dist = dijkstra(g, (0, 0), (h - 1, w - 1))
advent.print_answer(1, dist)


dist = dijkstra(g, (0, 0), (h - 1, w - 1), True)
advent.print_answer(2, dist)
