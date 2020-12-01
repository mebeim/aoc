#!/usr/bin/env python3

from utils import advent
from lib.intcode import IntcodeVM

EMPTY, WALL, BLOCK, PADDLE, BALL = range(5)


advent.setup(2019, 13)
fin = advent.get_input()

program = list(map(int, fin.read().split(',')))

vm = IntcodeVM(program)
out = vm.run()
blocks = set()

for i in range(0, len(out), 3):
	x, y, t = out[i:i + 3]
	if t == BLOCK:
		blocks.add((x, y))

total_blocks = len(blocks)
advent.print_answer(1, total_blocks)


vm.orig_code[0] = 2
vm.reset()

score    = 0
paddle_x = 0
inp      = []

while True:
	out = vm.run(inp, resume=True, n_out=3)
	if not out:
		break

	x, y, tile = out
	inp = [0]

	if (x, y) == (-1, 0):
		score = tile
		continue

	if tile == PADDLE:
		paddle_x = x
	elif tile == BALL:
		if x > paddle_x:
			inp[0] = 1
		elif x < paddle_x:
			inp[0] = -1

advent.print_answer(2, score)
