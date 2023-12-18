#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 18)
fin = advent.get_input()

sparse = set()
dirs = {
	'R': (0, 1),
	'L': (0, -1),
	'U': (-1, 0),
	'D': (1, 0),
}

r, c = 0, 0
for line in fin:
	d, n, x = line.split()
	n = int(n)
	dr, dc = dirs[d]

	for _ in range(n):
		r += dr
		c += dc

		sparse.add((r, c))

def inner_area(grid, main_loop):
	area = 0
	x = set()

	for r, row in enumerate(grid):
		inside = False

		for c, cell in enumerate(row):
			if (r, c) not in main_loop:
				area += inside
				if inside:
					x.add((r,c))
			else:
				inside = inside ^ (cell in '|F7')
				area += 1
				x.add((r,c))

	return area, x

minr, maxr = min(r for r, _ in sparse), max(r for r, _ in sparse)
minc, maxc = min(c for _, c in sparse), max(c for _, c in sparse)
sparse = set((r - minr, c - minc) for r, c in sparse)
# dump_sparse_matrix(sparse, '#.')

h = max(r for r, _ in sparse) + 1
w = max(c for _, c in sparse) + 1
new = [['.' for c in range (w)] for r in range(h)]

for r, row in enumerate(new):
	for c, _ in enumerate(row):
		if (r, c) in sparse:
			if (r+1, c) in sparse and (r, c+1) in sparse:
				new[r][c] = 'F'
			elif (r-1, c) in sparse and (r, c+1) in sparse:
				new[r][c] = 'L'
			elif (r-1, c) in sparse and (r, c-1) in sparse:
				new[r][c] = 'J'
			elif (r+1, c) in sparse and (r, c-1) in sparse:
				new[r][c] = '7'
			elif (r, c+1) not in sparse and (r, c-1) not in sparse:
				new[r][c] = '|'
			else:
				new[r][c] = '#'

ans1, x = inner_area(new, sparse)
# dump_sparse_matrix(x, '#.')
advent.print_answer(1, ans1)


dirs = {
	0: (0, 1),
	2: (0, -1),
	3: (-1, 0),
	1: (1, 0),
}

r, c = 0, 0
vertices = list()
perimeter = 0
fin.seek(0)

for line in fin:
	_, _, x = line.split()
	x = x[2:-1]
	d = int(x[-1])
	n = int(x[:-1], 16)
	dr, dc = dirs[d]
	r += n * dr
	c += n * dc
	vertices.append((r, c))
	perimeter += n

def shoelace(vertices):
	a = 0
	it1 = iter(vertices)
	it2 = iter(vertices)
	next(it2)

	for (r1, c1), (r2, c2) in zip(it1, it2):
		a += (r2 + r1)*(c2 - c1)

	(r1, c1) = vertices[-1]
	(r2, c2) = vertices[0]
	a += (r2 + r1)*(c2 - c1)

	a = abs(a) // 2
	return a

area = shoelace(vertices)
ans2 = int(area - perimeter / 2 + 1) + perimeter


advent.print_answer(2, ans2)
