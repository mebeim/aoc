#!/usr/bin/env python3

import sys

def sign(x):
	return (x > 0) - (x < 0)


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

DELTA = {'U': (0, 1), 'D': (0, -1), 'L': (-1, 0), 'R': (1, 0)}
rope  = [(0, 0)] * 10
seen1 = {(0, 0)}
seen9 = {(0, 0)}

for line in fin:
	direction, steps = line.split()
	steps = int(steps)

	for _ in range(steps):
		hx, hy = rope[0]
		dx, dy = DELTA[direction]
		rope[0] = hx + dx, hy + dy

		for i in range(9):
			hx, hy = rope[i]
			tx, ty = rope[i + 1]
			dx, dy = hx - tx, hy - ty

			if dx**2 + dy**2 > 2:
				rope[i + 1] = tx + sign(dx), ty + sign(dy)

		seen1.add(tuple(rope[1]))
		seen9.add(tuple(rope[9]))

answer1 = len(seen1)
answer2 = len(seen9)
print('Part 1:', answer1)
print('Part 2:', answer2)
