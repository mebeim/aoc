#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 7)
if 'debug' not in map(str.lower, sys.argv):
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
16,1,2
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


def fuel(ints, x):
	tot = 0
	for i in ints:
		tot += abs(i - x)
	return tot

def fuel2(ints, x):
	tot = 0
	for i in ints:
		start = min(x, i)
		end = max(x, i)
		m = end - start  +1
		lol = m  * (m-1) // 2
		tot += lol
	return tot

minf, minx = INFINITY, INFINITY
for x in range(min(ints), max(ints) + 1):
	f = fuel(ints, x)
	print(x, f)

	if f < minf:
		minf = f
		minx = x

ans = minf
print(minx)

advent.print_answer(1, ans)
# wait('Submit? ')
# advent.submit_answer(1, ans)


minf, minx = INFINITY, INFINITY
for x in range(min(ints), max(ints) + 1):
	f = fuel2(ints, x)

	if f < minf:
		minf = f
		minx = x

ans = minf


advent.print_answer(2, ans)
# wait('Submit? ')
# advent.submit_answer(2, ans)
