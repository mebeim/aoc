#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

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

print('Part 1:', answer1)
print('Part 2:', answer2)
