#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 10)
fin = advent.get_input()

grid2 = read_digit_matrix(fin)
ans1 = ans2 = 0


def dfs_count_9(grid, r, c):
	q = deque([(r, c)])
	seen = set()
	total = 0

	while q:
		node = q.pop()
		if node in seen:
			continue

		seen.add(node)
		r, c = node
		if grid[r][c] == 9:
			total += 1

		val = grid[r][c]
		for rr, cc in neighbors4(grid, r, c):
			if grid[rr][cc] == val + 1:
				q.append((rr, cc))

	return total

def dfs_count_path_to_9(grid, r, c):
	q = deque([((r, c), ((r, c),))])
	seen = set()
	paths = set()

	while q:
		node = q.pop()
		if node in seen:
			continue

		seen.add(node)
		(r, c), path = node
		if grid[r][c] == 9:
			paths.add(path)

		val = grid[r][c]
		for rr, cc in neighbors4(grid, r, c):
			if grid[rr][cc] == val + 1:
				q.append(((rr, cc), path + ((rr, cc))))

	return len(paths)

for r, row in enumerate(grid2):
	for c, x in enumerate(row):
		if x == 0:
			ans1 += dfs_count_9(grid2, r, c)

# 469 wrong
advent.print_answer(1, ans1)


for r, row in enumerate(grid2):
	for c, x in enumerate(row):
		if x == 0:
			ans2 += dfs_count_path_to_9(grid2, r, c)

advent.print_answer(2, ans2)
