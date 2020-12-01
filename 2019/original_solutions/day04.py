#!/usr/bin/env python3

from utils.all import *

fin = advent.get_input()
eprint(*fin, sep='')
timer_start()

##################################################

n = 0

for p in range(145852, 616942 + 1):
# for p in range(111122, 111122 + 1):
	s = str(p)
	x = tuple(map(int, s))
	a = x[0]

	tot = 1
	ok = False
	for b in x[1:]:
		if b == a:
			tot += 1
			if tot == 2:
				ok = True
				break
		a = b

	if ok:
		a = x[0]
		for b in x[1:]:
			if b < a:
				ok = False
				break
			a = b

	if ok:
		n += 1
		# print(p)

# 47 wrong answer
# 3756 wrong answer
advent.submit_answer(1, n)

n = 0

for p in range(145852, 616942 + 1):
# for p in range(111122, 111122 + 1):
	s = str(p)
	x = tuple(map(int, s))
	a = x[0]

	tot = 1
	ok = False
	for b in x[1:]:
		if b == a:
			tot += 1
			if tot == 3:
				ok = False
		else:
			if tot == 2:
				ok = True
				break
			tot = 1
		a = b

	if tot == 2:
		ok = True

	if ok:
		a = x[0]
		for b in x[1:]:
			if b < a:
				ok = False
				break
			a = b

	if ok:
		n += 1
		# print(p)

# 816 wrong answer
# 938 wrong answer
# 990 wrong answer
advent.submit_answer(2, n)
