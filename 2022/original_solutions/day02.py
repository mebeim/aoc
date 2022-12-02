#!/usr/bin/env python3

from utils.all import *

advent.setup(2022, 2)

DEBUG = 'debug' in map(str.lower, sys.argv)
if not DEBUG:
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
A Y
B X
C Z
''')

lines = get_lines(fin); fin.seek(0, 0)
ans = 0

for line in lines:
	a, b = line.strip().split()
	ab = a + b

	if ab == 'AX': # ro ro = dra
		ans += 3 + 1
	elif ab == 'AY': # ro pa = wi
		ans += 6 + 2
	elif ab == 'AZ': # ro sci = lose
		ans += 0 + 3

	elif ab == 'BX': # paper rock = lose
		ans += 0 + 1
	elif ab == 'BY': # paper paper = dr
		ans += 3 + 2
	elif ab == 'BZ':
		ans += 6 + 3 # paper scis = win

	elif ab == 'CX':
		ans += 6 + 1 # sci rock = win
	elif ab == 'CY':
		ans += 0 + 2 # sci pap = lose
	elif ab == 'CZ':
		ans += 3 + 3 # sci sci = draw
	else:
		assert ab

# 10851 wrong
advent.print_answer(1, ans)


ans = 0
for line in lines:
	a, b = line.strip().split()
	ab = a + b

	if ab == 'AX': # ro lose
		ans += 0 + 3
	elif ab == 'AY': # ro dra
		ans += 3 + 1
	elif ab == 'AZ': # ro wi
		ans += 6 + 2

	elif ab == 'BX': # paper lose
		ans += 0 + 1
	elif ab == 'BY': # paper dra
		ans += 3 + 2
	elif ab == 'BZ':
		ans += 6 + 3 # paper wi

	elif ab == 'CX':
		ans += 0 + 2 # sci lose
	elif ab == 'CY':
		ans += 3 + 3 # sci dra
	elif ab == 'CZ':
		ans += 6 + 1 # sci win
	else:
		assert ab

advent.print_answer(2, ans)
