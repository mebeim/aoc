#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 11)
if 'debug' not in map(str.lower, sys.argv):
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
5483143223
2745854711
5264556173
6141336146
6357385478
4167524645
2176841721
6882881134
4846848554
5283751526
''')

eprint(*fin, sep='', end='----- end of input -----\n\n'); fin.seek(0, 0)
timer_start()

ans = 0
try: ints = get_ints(fin, True); fin.seek(0, 0)
except: pass
try: lines = get_lines(fin); fin.seek(0, 0)
except: pass
try: mat = get_char_matrix(fin, rstrip=False, lstrip=False); fin.seek(0, 0)
except: pass

mat = [[int(x) for x in row] for row in mat]


def flash(mat):
	flashed = set()
	done = False

	# flash all flashable
	while not done:
		for r, row in enumerate(mat):
			for c, x in enumerate(row):
				if x > 9 and (r, c) not in flashed:
					flashed.add((r, c))

					for nr, nc in neighbors8(mat, r, c, ()):
						mat[nr][nc] += 1

		# any more?
		done = True
		for r, row in enumerate(mat):
			for c, x in enumerate(row):
				if x > 9 and (r, c) not in flashed:
					done = False

	for r, c in flashed:
		mat[r][c] = 0

	return len(flashed)

def evolve(mat, n):
	nflashes = 0
	tot = len(mat) * len(mat[0])

	for day in range(1, n):
		for r, row in enumerate(mat):
			for c, x in enumerate(row):
				mat[r][c] += 1

		nn = flash(mat)
		if nn == tot:
			advent.print_answer(2, day)
			wait('Submit? ')
			advent.submit_answer(2, day)
			sys.exit(0)

		nflashes += nn

	return nflashes


for l in mat:
	print(''.join(map(str, l)))
print('--')

# ans = evolve(mat, 100)
ans = evolve(mat, 10000000)

for l in mat:
	print(''.join(map(str, l)))
print('--')

advent.print_answer(1, ans)
wait('Submit? ')
advent.submit_answer(1, ans)
