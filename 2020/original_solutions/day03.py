#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 3)
fin = advent.get_input()
# eprint(*fin, sep=''); fin.seek(0, 0)
timer_start()

orig = get_char_matrix(fin)

h = len(orig)
w = len(orig[0])
print(h, w)

mat = copy.deepcopy(orig)

n = 0
i = 0
j = 0

while i < h:
	if mat[i][j % w] == '#':
		mat[i][j % w] = 'X'
		n += 1
	else:
		mat[i][j % w] = 'O'

	i += 1
	j += 3

assert 'X' in mat[-1] or 'O' in mat[-1]
advent.submit_answer(1, n)


mat = copy.deepcopy(orig)
tot = 1
for dj, di in ((1,1 ), (3, 1), (5, 1), (7, 1), (1, 2)):
	n = 0
	i = 0
	j = 0

	while i < h:
		if mat[i][j % w] == '#':
			n += 1

		i += di
		j += dj

	tot *= n

advent.submit_answer(2,tot)
