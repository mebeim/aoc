#!/usr/bin/env python3

from time import daylight
from utils.all import *

advent.setup(2021, 6)
if 'debug' not in map(str.lower, sys.argv):
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
3,4,3,1,2
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

fish = list()

for f in ints:
	fish.append(f)

print(fish)

for i in range(1, 80+1):
	newfish = list()

	for left in fish:
		left -= 1

		if left < 0:
			newfish.append(8)
			newfish.append(6)
		else:
			newfish.append(left)

	fish = newfish
	# eprint(i, newfish)

ans = len(fish)

advent.print_answer(1, ans)
# wait('Submit? ')

fish = defaultdict(int)

for f in ints:
	fish[f] += 1
print(fish)

day = 0

for i in range(1, 256 + 1):
	newfish = defaultdict(int)

	for k, n in fish.items():
		k -= 1

		if k < 0:
			newfish[8] += n
			newfish[6] += n
		else:
			newfish[k] += n

	fish = newfish
	# print(i, sum(fish.values()), fish)

ans = sum(fish.values())

advent.print_answer(2, ans)
wait('Submit? ')
advent.submit_answer(2, ans)
