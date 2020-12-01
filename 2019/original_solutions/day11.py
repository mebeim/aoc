#!/usr/bin/env python3

from utils.all import *
from lib.intcode import IntcodeVM

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

program = get_ints(fin, True)

BLACK, WHITE = 0, 1
LEFT, RIGHT = 0, 1

NORTH, SOUTH, EAST, WEST = 'NSEW'

robot = IntcodeVM(program)
grid = defaultdict(lambda: BLACK)
pos = (0,0)

############## Uncomment for part 2 ############
# grid[pos] = WHITE
################################################

curdir = NORTH
first = True
deb = False

while True:
	# print(curdir, pos, grid[pos] if pos in grid else '?')

	if first:
		out = robot.run([grid[pos]], n_out=2, debug=deb)
		first = False
	else:
		out = robot.run([grid[pos]], n_out=2, resume=True, debug=deb)

	if not out:
		break

	color, dirr = out
	grid[pos] = color

	if dirr == LEFT:
		if curdir == NORTH:
			curdir = WEST
			pos = (pos[0], pos[1] - 1)
		elif curdir == SOUTH:
			curdir = EAST
			pos = (pos[0], pos[1] + 1)
		elif curdir == EAST:
			curdir = NORTH
			pos = (pos[0] - 1, pos[1])
		elif curdir == WEST:
			curdir = SOUTH
			pos = (pos[0] + 1, pos[1])
	elif dirr == RIGHT:
		if curdir == NORTH:
			curdir = EAST
			pos = (pos[0], pos[1] + 1)
		elif curdir == SOUTH:
			curdir = WEST
			pos = (pos[0], pos[1] - 1)
		elif curdir == EAST:
			curdir = SOUTH
			pos = (pos[0] + 1, pos[1])
		elif curdir == WEST:
			curdir = NORTH
			pos = (pos[0] - 1, pos[1])
	else:
		assert False, 'wtf'

tot = len(grid)

# 843 not right
# 842 not right
advent.submit_answer(1, tot)

print(min(grid), max(grid))

for i in range(0, 10):
	for j in range(0, 40):
		if grid[i,j] == BLACK:
			sys.stdout.write(' ')
		else:
			sys.stdout.write('#')
	sys.stdout.write('\n')

# advent.submit_answer(2, ans2)
