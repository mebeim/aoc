#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 16)

fin = advent.get_input()
grid = read_char_matrix(fin)

ans1 = ans2 = 0
g = defaultdict(list)

for r, row in enumerate(grid):
	for c, char in enumerate(row):
		if char == 'S':
			start = Vec(r, c)
		if char == 'E':
			end = Vec(r, c)

		for nr, nc in neighbors4(grid, r, c):
			if grid[nr][nc] != '#':
				g[Vec(r,c)].append(Vec(nr, nc))


def angle(a, b):
	d = b - a
	if abs(d.r) == 2 or abs(d.c) == 2:
		return 2000
	if abs(d.r) == 1 or abs(d.c) == 1:
		return 1000
	return 0


def explore(src, dst, face):
	q = [(0, src, face, frozenset([src]))]
	distance = defaultdict(lambda: INFINITY)
	best_path_points = set()
	best = INFINITY

	while q:
		score, pos, face, path = heapq.heappop(q)
		if pos == dst:
			if score < best:
				best = score
				best_path_points = path
			elif score == best:
				best_path_points |= path
			continue

		k = pos, face
		if distance[k] < score:
			continue

		distance[k] = score

		for n in g[pos]:
			if n in path:
				continue

			direction = n - pos
			a = angle(face, direction)
			heapq.heappush(q, (score + a + 1, n, direction, path | {n}))

	return best, len(best_path_points)


ans1, ans2 = explore(start, end, Vec(0, 1))
advent.print_answer(1, ans1)
advent.print_answer(2, ans2)
