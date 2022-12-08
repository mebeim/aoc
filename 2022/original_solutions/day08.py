#!/usr/bin/env python3

from utils.all import *

advent.setup(2022, 8)

DEBUG = 'debug' in map(str.lower, sys.argv)
if not DEBUG:
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
30373
25512
65332
33549
35390
''')

mat = get_char_matrix(fin, rstrip=True, lstrip=True)

imat = []
for l in mat:
	imat.append(list(map(int, l)))
# print(imat)
mat = imat

ans = 0

for r, row in enumerate(mat):
	for c, cell in enumerate(row):
		vis = True

		for i in range(c + 1, len(mat[0])):
			if mat[r][i] >= cell:
				vis = False

		if vis:
			ans += 1
			continue

		vis = True

		for i in range(c - 1, -1, -1):
			if mat[r][i] >= cell:
				vis = False

		if vis:
			ans += 1
			continue

		vis = True

		for i in range(r + 1, len(mat)):
			if mat[i][c] >= cell:
				vis = False

		if vis:
			ans += 1
			continue

		vis = True

		for i in range(r - 1, -1, -1):
			if mat[i][c] >= cell:
				vis = False

		if vis:
			ans += 1

advent.print_answer(1, ans)


best = 0

for r, row in enumerate(mat):
	for c, cell in enumerate(row):
		l,rr,u,d = 0, 0, 0, 0

		for i in range(c + 1, len(mat[0])):
			rr += 1
			if mat[r][i] >= cell:
				break

		for i in range(c - 1, -1, -1):
			l += 1
			if mat[r][i] >= cell:
				break

		for i in range(r + 1, len(mat)):
			d += 1
			if mat[i][c] >= cell:
				break

		for i in range(r - 1, -1, -1):
			u += 1
			if mat[i][c] >= cell:
				break

		# print(r, c, '/', u, l, rr, d)

		vd = l * rr * u *d
		if vd > best:
			best = vd

advent.print_answer(2, best)
