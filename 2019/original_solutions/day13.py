#!/usr/bin/env python3

from utils.all import *
from lib.intcode import IntcodeVM

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

program = get_ints(fin, True)

vm = IntcodeVM(program)
screen = set()

out = vm.run()

for i in range(0, len(out), 3):
	x, y, t = out[i: i + 3]
	if t == 2:
		screen.add((x, y))
# 	if t == 3:
# 		paddle = x, y
# 		print(paddle)

# print(paddle)

advent.submit_answer(1, len(screen))

# def display(screen):
# 	minx = min(x for x, _ in screen)
# 	maxx = max(x for x, _ in screen)
# 	miny = min(y for _, y in screen)
# 	maxy = max(y for _, y in screen)

# 	height = maxy - miny + 1
# 	width = maxx - minx + 1

# 	grid = [[' '] * width for _ in range(height)]

# 	for y in range(height):
# 		for x in range(width):
# 			grid[y][x] = TILEMAP[screen[x + minx, y + miny]]

# 	s = '\n'.join(''.join(grid[y]) for y in range(height))
# 	sys.stdout.write(s + '\n')
# 	sys.stdout.flush()


TILEMAP = ' +#=o'
EMPTY, WALL, BLOCK, PADDLE, BALL = range(5)

program[0] = 2
vm = IntcodeVM(program)

screen = defaultdict(lambda: EMPTY)
score = 0
nblocks = 304
inp = []
make_move = False
paddlex = 0
frames = 0

from time import sleep

while True:
	out = vm.run(inp, resume=True, n_out=3)
	if not out:
		break

	x, y, tile = out
	# print(frames, x, y, tile)

	inp = [0]

	if (x, y) == (-1, 0):
		score = tile
		# print('--->', score)
	else:
		screen[x, y] = tile

		if tile == BALL and make_move:
			if x > paddlex:
				inp = [1]
			elif x < paddlex:
				inp = [-1]

			make_move = False
		elif tile == PADDLE and not make_move:
			paddlex = x
			make_move = True

	# if frames < 1050:
	# 	frames += 1
	# else:
	# 	sleep(0.05)
	# 	display(screen)

advent.submit_answer(2, score)
