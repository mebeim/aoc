#!/usr/bin/env python3

from utils import advent

def sign(x):
	return (x > 0) - (x < 0)


advent.setup(2022, 9)

DELTA = {'U': (0, 1), 'D': (0, -1), 'L': (-1, 0), 'R': (1, 0)}
rope  = [(0, 0)] * 10
seen1 = {(0, 0)}
seen9 = {(0, 0)}

with advent.get_input() as fin:
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
advent.print_answer(1, answer1)
advent.print_answer(2, answer2)
