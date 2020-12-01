#!/usr/bin/env python3

from utils.all import *

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

from lib.intcode import IntcodeVM
prog = get_ints(fin, True)
vm = IntcodeVM(prog)

n = 0
for i in range(50):
	for j in range(50):
		out = vm.run([i, j], n_out=1)
		if not out:
			break
		if out[0] == 1:
			n += 1

# print(n)
advent.submit_answer(1, n)

# PART 2:
# Visualize, copy in text editor and solve by hand
# using a regex: (1{100}.+\n){100}

starty, startx = 350, 1050 + (150 - 127)
width, height = 150, 200
# grid = [[-1] * width for _ in range(height)]
# foundx = 0

# for x in range(width):
# 	log('> {}\r   ', x)

# 	n = 0
# 	for y in range(height):
# 		res = intcode_oneshot(prog, [x+startx, y+starty])[0]
# 		n += res
# 		grid[y][x] = res

# 	if n == 134:
# 		if foundx == 0:
# 			foundx = x

# conv = dict(zip(range(-1, 100), '! #'))
# vizgrid = []

# for l in grid:
# 	a = ''.join(map(lambda v: conv.get(v, '?'), l))
# 	a = ''.join(map(str, l))
# 	vizgrid.append(a)

# dump_iterable(vizgrid)

foundx = 0
x = foundx + startx
y = starty + 61

answer = x * 10000 + y

# 13440699 wrong (1195, 549)
# 11950549 wrong (1344, 699) of course...
# 10670533 wrong (1067, 533)
# 10730533 wrong (1073, 533)
advent.submit_answer(2, answer)

