#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 13)
if 'debug' not in map(str.lower, sys.argv):
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
0,0
2,2

fold along y=1
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

sheet = {}

for l in fin:
	l = l.strip()
	if not l:
		break

	x, y = map(int, l.split(','))
	sheet[x, y] = 1


foldx = int(fin.readline().split('=')[1])

new = {}

for x, y in sheet:
	if x > foldx:
		x = foldx - abs(x - foldx)

	new[x, y] = 1

ans = len(new)


advent.print_answer(1, ans)
# wait('Submit? ')
# advent.submit_answer(1, ans)

sheet = new

for line in fin:
	line = line.strip()
	if not line:
		continue

	if 'x=' in line:
		foldx = int(line.split('=')[1])

		new = {}

		for x, y in sheet:
			if x > foldx:
				x = foldx - abs(x - foldx)

			new[x, y] = 1

		sheet = new

	else:
		foldy = int(line.split('=')[1])

		new = {}

		for x, y in sheet:
			if y > foldy:
				y = foldy - abs(y - foldy)

			new[x, y] = 1

		sheet = new

maxx = max(map(itemgetter(0), sheet))
maxy = max(map(itemgetter(1), sheet))

for y in range(maxy+1):
	for x in range(maxx+1):
		if (x, y) in sheet:
			log('#')
		else:
			log(' ')
	log('\n')

