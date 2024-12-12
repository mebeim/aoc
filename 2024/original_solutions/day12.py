#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 12)
fin = advent.get_input()

grid = read_char_matrix(fin)

ans1 = ans2 = 0
g = defaultdict(set)

for r, row in enumerate(grid):
	for c, char in enumerate(row):
		for rr, cc in neighbors4(grid, r, c):
			g[r,c]
			if grid[rr][cc] == char:
				g[r,c].add((rr, cc))
				g[rr,cc].add((r, c))

comps = connected_components(g)
# dump_iterable(comps)

def perimeter(comp):
	perim = 0
	for r, c in comp:
		for n in neighbors4_coords(r, c):
			if n not in comp:
				perim += 1
	return perim

def area(comp):
	return len(comp)

def sides(comp):
	uside, dside, lside, rside = UnionFind(), UnionFind(), UnionFind(), UnionFind()
	U, D, L, R = (0, -1), (0, 1), (-1, 0), (1, 0)

	for v in starmap(Vec, comp):
		if v + U not in comp:
			uside.add(v)
		if v + D not in comp:
			dside.add(v)
		if v + L not in comp:
			lside.add(v)
		if v + R not in comp:
			rside.add(v)

	for v in uside.elements:
		for d in (L, R):
			if v + d in uside:
				uside.union(v, v + d)

	for v in dside.elements:
		for d in (L, R):
			if v + d in dside:
				dside.union(v, v + d)

	for v in lside.elements:
		for d in (U, D):
			if v + d in lside:
				lside.union(v, v + d)

	for v in rside.elements:
		for d in (U, D):
			if v + d in rside:
				rside.union(v, v + d)

	return uside.size + dside.size + lside.size + rside.size


# for comp in comps:
# 	print(comp)
# 	print(area(comp))
# 	print(perimeter(comp))
# 	print(sides(comp))

ans1 = sum(area(comp) * perimeter(comp) for comp in comps)
advent.print_answer(1, ans1)

# 649082 wrong
ans2 = sum(area(comp) * sides(comp) for comp in comps)
advent.print_answer(2, ans2)
