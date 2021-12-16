#!/usr/bin/env python3

from re import UNICODE
from utils.all import *

advent.setup(2021, 9)
if 'debug' not in map(str.lower, sys.argv):
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
2199943210
3987894921
9856789892
8767896789
9899965678
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

chmat = deepcopy(mat)
mat = list(map(lambda x: list(map(int, x)), mat))

for r, row in enumerate(mat):
	for c, h in enumerate(row):
		ok = True

		for dr,dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
			try:
				if mat[r+dr][c+dc] <= h:
					ok = False
			except:
				pass

		if ok:
			# chmat[r][c] = '*'
			ans += h + 1

# dump_char_matrix(chmat)

# 1702 wrong
advent.print_answer(1, ans)
# wait('Submit? ')
# advent.submit_answer(1, ans)

basins = []
p2b = defaultdict(set)

for r, row in enumerate(chmat):
	for c, h in enumerate(row):
		if h == '9' or any((r, c) in b for b in basins):
			continue

		s = set([(r, c)])
		prev = set()
		bad = False

		while prev != s:
			new = deepcopy(s)
			for src in s:
				for rcc, d in grid_find_adjacent(chmat, src, '012345678', '9', True):
					rc = (rcc[0], rcc[1])
					new.add(rc)
			prev = s
			s = new

		# if any(rc in b for b in basins):
			# bad = True

		# if not bad:
		basins.append(s)


print(len(basins))
dump_iterable(basins)

# for b in basins[:2]:
# 	for r, c in b:
# 		chmat[r][c] = '*'

# dump_char_matrix(chmat)

# for rcc, d in grid_find_adjacent(chmat, (0, 5), '012345678', '9', True):
# 	rc = (rcc[0], rcc[1])
# 	print(rc)

ans = 1
ss = sorted(map(len, basins), reverse=1)[:3]
for s in ss:
	ans *= s


advent.print_answer(2, ans)
wait('Submit? ')
advent.submit_answer(2, ans)
