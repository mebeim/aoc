#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 21)
fin = advent.get_input()
grid = fin.read().splitlines()

def grid_bfs(grid, src, maxdist, get_neighbors=neighbors4):
	queue   = deque([(0, src)])
	visited = set()
	tot = 0
	parity = maxdist % 2

	while queue:
		dist, rc = queue.popleft()
		if dist > maxdist:
			break

		if rc in visited:
			continue

		if dist % 2 == parity:
			tot += 1

		visited.add(rc)

		for n in filterfalse(visited.__contains__, get_neighbors(grid, *rc, '#')):
			queue.append((dist + 1, n))

	return tot

def p2_neighbors(grid, r, c, _):
	for rr, cc in neighbors4_coords(r, c):
		if grid[rr % H][cc % W] != '#':
			yield rr, cc


for r, row in enumerate(grid):
	for c, char in enumerate(row):
		if char == 'S':
			start = (r, c)
			break

W, H = len(grid[0]), len(grid)
assert H == W

ans1 = grid_bfs(grid, start, 64)
advent.print_answer(1, ans1)

mod = 26501365 % H

# prev = 0
# diffs = []
# for i in range(6):
# 	x = grid_bfs(grid, start, mod + H * i, p2_neighbors)
# 	print(i, mod + H * i, x, x - prev)
# 	diffs.append(x - prev)
# 	prev = x

# for a, b in zip(diffs, diffs[1:]):
# 	print(b - a)

a = grid_bfs(grid, start, mod, p2_neighbors)
b = grid_bfs(grid, start, mod + H, p2_neighbors)
c = grid_bfs(grid, start, mod + 2*H, p2_neighbors)

first_diff1 = b - a
first_diff2 = c - b
second_diff = first_diff2 - first_diff1

# https://www.radfordmathematics.com/algebra/sequences-series/difference-method-sequences/quadratic-sequences.html
A = second_diff // 2
B = first_diff1 - 3 * A
C = a - B - A
f = lambda n: A*n**2 + B*n + C

# print(f'f(n) = {A}n^2 + {B}n + {C}')
# for i in range(10):
# 	print(i, f(i))

# f(n) = num of reachable cells in n * H steps
ans2 = f(ceil(26501365 / H))
advent.print_answer(2, ans2)
