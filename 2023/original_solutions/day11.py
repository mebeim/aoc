#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 11)
fin = advent.get_input()

grid = read_char_matrix(fin)
newgrid = []
insert = []
original = deepcopy(grid)

for c in range(len(grid[0])):
	if all(grid[r][c] == '.' for r in range(len(grid))):
		insert.append(c + len(insert))

for c in insert:
	for row in grid:
		row.insert(c, '.')

for r, row in enumerate(grid):
	newgrid.append(row[:])
	if set(row) == {'.'}:
		newgrid.append(row[:])

grid = newgrid

g = graph_from_grid(newgrid, '#', '.', True)
ks = list(g.keys())
ans = 0

for i, src in enumerate(ks):
	for dst in ks[i+1:]:
		a = Vec(*src[:2])
		b = Vec(*dst[:2])
		d = a - b
		ans += abs(d.r) + abs(d.c)

advent.print_answer(1, ans)


vertical = []
horizontal = []
expansion = 1000000 - 1
grid = original

for c in range(len(grid[0])):
	if all(grid[r][c] == '.' for r in range(len(grid))):
		vertical.append(c)

for r, row in enumerate(grid):
	if set(row) == {'.'}:
		horizontal.append(r)

ans = 0
g = graph_from_grid(original, '#', '.', True)
ks = list(g.keys())

for i, src in enumerate(ks):
	for dst in ks[i+1:]:
		a = Vec(*src[:2])
		b = Vec(*dst[:2])

		rfrom, rto = min(a.r, b.r), max(a.r, b.r)
		cfrom, cto = min(a.c, b.c), max(a.c, b.c)
		d = rto - rfrom + cto - cfrom

		for h in horizontal:
			if h >= rto:
				break
			if rfrom < h < rto:
				d += expansion

		for v in vertical:
			if v >= cto:
				break
			if cfrom < v < cto:
				d += expansion

		ans += d

advent.print_answer(2, ans)
