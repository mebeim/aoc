#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

total = 0
cycle = 1
x     = 1
crt   = ''

for instr in fin:
	crt   += '#' if x <= cycle % 40 < x + 3 else ' '
	cycle += 1

	if instr.startswith('addx'):
		if cycle % 40 == 20:
			total += cycle * x
		elif cycle % 40 == 1:
			crt += '\n'

		crt   += '#' if x <= cycle % 40 < x + 3 else ' '
		cycle += 1
		x     += int(instr[5:])

	if cycle % 40 == 20:
		total += cycle * x
	elif cycle % 40 == 1:
		crt += '\n'

print('Part 1:', total)
print('Part 2:', crt, sep='\n', end='')
