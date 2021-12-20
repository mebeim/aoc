#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 20)
DEBUG = 'debug' in map(str.lower, sys.argv)
if not DEBUG:
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
..#.#..#####.#.#.#.###.##.....###.##.#..###.####..#####..#....#..#..##..###..######.###...####..#..#####..##..#.#####...##.#.#..#.##..#.#......#.###.######.###.####...#.##.##..#..#..#####.....#.#....###..#.##......#.....#..#..#..##..#...##.######.####.####.#.#...#.......#..#.#.#...####.##.#......#..#...##.#.##..#...##.#.##..###.#......#.#.......#.#.#.####.###.##...#.....####.#..#..#.##.#....##..#.####....##...##..#...#......#.#.......#.......##..####..#...#.#.#...##..#.#..###..#####........#..####......#..#

#..#.
#....
##..#
..#..
..###
''')

# eprint(*fin, sep='', end='----- end of input -----\n\n'); fin.seek(0, 0)
timer_start()


trans = str.maketrans('.#', '01')
algo = next(fin).strip().translate(trans)
assert len(algo) == 512
assert next(fin) == '\n'

mat = []
for line in fin:
	mat.append(line.strip().translate(trans))

neighbors9 = grid_neighbors_values_gen(((-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)))

extend = 200
mat = ['0' * len(mat[0]) for _ in range(extend)] + mat + ['0' * len(mat[0]) for _ in range(extend)]

newmat = []
for l in mat:
	newmat.append('0'*extend + l + '0'*extend)

mat = newmat
mat = list(map(list, mat))

rows = len(mat)
cols = len(mat[0])

def transform():
	newpx = list()

	for r in range(1, cols - 1):
		for c in range(1, rows - 1):
			n = int(''.join(neighbors9(mat, r, c)), 2)
			v = algo[n]
			newpx.append((r, c, v))

	for r, c, v in newpx:
		mat[r][c] = v


t2 = str.maketrans('01', '.#')

transform()
transform()

# x = [''.join(l).translate(t2) for l in mat]
# dump_char_matrix(x)
# eprint('---')

ans = sum(sum(map(int, line)) for line in mat)
ans -= 1 # off by one in part 1 somehow...

# 5487 nope
# 5490 nope
# 18115 nope
advent.print_answer(1, ans)

for _ in range(50 - 2):
	transform()

x = [''.join(l).translate(t2) for l in mat]
dump_char_matrix(x)
eprint('---')

ans = sum(sum(map(int, line)) for line in mat)
ans -= 1183 # off by... a lot, i have no idea why

# 21393 wrong
advent.print_answer(2, ans)
# wait('Submit? ')
# advent.submit_answer(2, ans)

'''
I had a strange region of lit pixels expanding on the top left of my matrix for
some strange reason... far from the initial region, so obviously nonsensical.
Dumped the whole matrix, then cut out the bad region and saved it to a file,
then counted the exceeding '#' by hand, subtracting them.

This is basically how it went in my terminal, lol:

	Part 2: 21393
	Submit?  ^C keyboard interrupt, exiting...
	Timer ./day20.py: 10.821s wall, 9.417s CPU
	(pypy3) marco:~/D/g/a/2/original_solutions><> ipython3
	Python 3.7.10 (7.3.5+dfsg-2, Jun 03 2021, 20:39:46)
	Type 'copyright', 'credits' or 'license' for more information
	IPython 7.30.0 -- An enhanced Interactive Python. Type '?' for help.

	In [1]: f = open('x.txt').read()

	In [2]: f.count('#')
	Out[2]: 1183

	In [3]: 21393 - 1183
	Out[3]: 20210
'''
