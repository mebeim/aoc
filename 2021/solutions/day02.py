#!/usr/bin/env python3

from utils import advent

advent.setup(2021, 2)
fin = advent.get_input()

aim = horiz = depth1 = depth2 = 0

for line in fin:
	cmd, x = line.split()
	x = int(x)

	if cmd == 'down':
		depth1 += x
		aim    += x
	elif cmd == 'up':
		depth1 -= x
		aim    -= x
	else:
		horiz  += x
		depth2 += aim * x

answer1 = horiz * depth1
answer2 = horiz * depth2

advent.print_answer(1, answer1)
advent.print_answer(2, answer2)
