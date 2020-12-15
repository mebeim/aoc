#!/usr/bin/env python3
#
# Run with PyPy unless you want to wait a looong time...
#

from utils.all import *

advent.setup(2020, 15)
fin = advent.get_input()
timer_start()

nums = get_ints(fin, True)
# nums = [1,3,2]
# nums = [0,3,6]

said = defaultdict(list, {n: [i] for i, n in enumerate(nums, 1)})
counts = defaultdict(int, {n: 1 for n in nums})
turn = len(nums) + 1
last = nums[-1]

while turn < 2021:
	if counts[last] == 1:
		n = 0
		# eprint('0 - last was just seen')
	elif counts[last] > 1:
		n = said[last][-1] - said[last][-2]
		# eprint(f'{n} - last two turns were {said[last][-1]} and {said[last][-2]}')
	else:
		assert False

	# eprint(n)
	counts[n] += 1
	said[n].append(turn)
	last = n
	turn += 1

advent.print_answer(1, n)


while turn < 30000001:
	# if turn % 100000 == 0:
	# 	eprint(turn)
	if counts[last] == 1:
		n = 0
	elif counts[last] > 1:
		n = said[last][-1] - said[last][-2]

	counts[n] += 1
	said[n].append(turn)
	last = n
	turn += 1

advent.print_answer(2, n)
