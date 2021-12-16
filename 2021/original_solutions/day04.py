#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 4)
if 'debug' not in map(str.lower, sys.argv):
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
7,4,9,5,11,17,23,2,0,14,21,24,10,16,13,6,15,25,12,22,18,20,8,19,3,26,1

22 13 17 11  0
 8  2 23  4 24
21  9 14 16  7
 6 10  3 18  5
 1 12 20 15 19

 3 15  0  2 22
 9 18 13 17  5
19  8  7 25 23
20 11 10 24  4
14 21 16 12  6

14 21 17 24  4
10 16 15  9 19
18  8 23 26 20
22 11 13  6  5
 2  0 12  3  7
''')

eprint(*fin, sep='', end='----- end of input -----\n\n'); fin.seek(0, 0)

timer_start()
stuff = fin.read().split('\n\n')

nums = tuple(map(int, stuff[0].split(',')))
print(nums)
mats = []
for s in stuff[1:]:
	lines = s.splitlines()
	mat = []
	for l in lines:
		l = list(map(int, l.split()))
		mat.append(l)
	mats.append(mat)

def checkwin(mat):
	for l in mat:
		rtot = sum(1 if x is None else 0 for x in l)
		if rtot == 5:
			return True

	for l in zip(*mat):
		rtot = sum(1 if x is None else 0 for x in l)
		if rtot == 5:
			return True

okmats = deepcopy(mats)
nwins = 0
won = set()

for turn, chosen in enumerate(nums):
	for i, (mat, okmat) in enumerate(zip(mats, okmats)):
		for r, l in enumerate(mat):
			for c, xx in enumerate(l):
				if xx == chosen:
					okmat[r][c] = None

					if i not in won and checkwin(okmat):
						win = 0
						nwins += 1
						won.add(i)
						print('num', nwins, 'to win is', i)

						if nwins == 1 or nwins == len(mats):
							for R, ROK in zip(mat, okmat):
								for N, NOK in zip(R, ROK):
									if NOK is not None:
										win += N

							ans = win * chosen

							if nwins == 1:
								advent.print_answer(1, ans)
								# wait('Submit? ')
								# advent.submit_answer(1, ans)

							else:
								if nwins == len(mats):
									print(turn, chosen)
									print(i)
									advent.print_answer(2, ans)
									wait('Submit? ')
									advent.submit_answer(2, ans)
