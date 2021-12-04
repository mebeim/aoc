#!/usr/bin/env python3

from utils import advent

advent.setup(2021, 2)
fin = advent.get_input()

aim = horiz = depth = 0

for line in fin:
	cmd, x = line.split()
	x = int(x)

	if cmd == 'down':
		aim += x
	elif cmd == 'up':
		aim -= x
	else:
		horiz += x
		depth += aim * x

answer1 = horiz * aim
answer2 = horiz * depth

advent.print_answer(1, answer1)
advent.print_answer(2, answer2)
