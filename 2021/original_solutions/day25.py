#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 25)

DEBUG = 'debug' in map(str.lower, sys.argv)
if not DEBUG:
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
v...>>.vv>
.vv>>.vv..
>>.>v>...v
>>v>>.>.v.
v>v.vv.v..
>.>>..v...
.vv..>.>v.
v.v..>>v.v
....v..v.>
''')

mat = get_char_matrix(fin, rstrip=False, lstrip=False)

def step(mat):
	n = 0

	while 1:
		done = True
		w = len(mat[0])
		h = len(mat)
		newmat = [['.' for _ in range(w)] for _ in range(h)]

		for r, row in enumerate(mat):
			for c, cell in enumerate(row):
				if cell == '>':
					rr, cc = r, (c + 1) % w

					# eprint(r, c, cell, '|', rr, cc, mat[r][(c + 1) % w])

					if mat[rr][cc] == '.':
						newmat[rr][cc] = '>'
						done = False
					else:
						newmat[r][c] = '>'
				elif cell == 'v':
					newmat[r][c] = cell

		mat = newmat
		newmat = [['.' for _ in range(w)] for _ in range(h)]

		for r, row in enumerate(mat):
			for c, cell in enumerate(row):
				if cell == 'v':
					rr, cc = (r + 1) % h, c

					# eprint(r, c, cell, '|', rr, cc, mat[rr][cc])

					if mat[rr][cc] == '.':
						newmat[rr][cc] = 'v'
						done = False
					else:
						newmat[r][c] = cell
				elif cell == '>':
					newmat[r][c] = cell

		n += 1
		mat = newmat

		# eprint(n)
		# dump_char_matrix(mat)
		# eprint('')

		if done:
			break

	return n


ans = step(mat)
advent.print_answer(1, ans)
