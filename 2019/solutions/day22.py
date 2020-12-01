#!/usr/bin/env python3

from utils import advent

DEAL_NEW, DEAL_INC, CUT = 0, 1, 2

def build_moves(instructions):
	moves = []

	for l in instructions:
		if 'deal into' in l:
			moves.append((DEAL_NEW, 0))
		elif 'deal with' in l:
			n = int(l[l.rfind(' '):])
			moves.append((DEAL_INC, n))
		elif 'cut' in l:
			n = int(l[l.rfind(' '):])
			moves.append((CUT, n))

	return moves

def transform(start, step, size, moves):
	for move, n in moves:
		if move == DEAL_NEW:
			start = (start - step) % size
			step = -step % size
		elif move == DEAL_INC:
			step = (step * pow(n, size - 2, size)) % size
		elif move == CUT:
			if n < 0:
				n += size

			start = (start + step * n) % size

	return start, step

def repeat(start, step, size, repetitions):
	final_step = pow(step, repetitions, size)
	S = (1 - final_step) * pow(1 - step, size - 2, size)
	final_start = (start * S) % size

	return final_start, final_step


advent.setup(2019, 22, 1)
fin = advent.get_input()

moves = build_moves(fin)
start, step, size = 0, 1, 10007
target_card = 2019

start, step = transform(start, step, size, moves)
position = ((target_card - start) * pow(step, size - 2, size)) % size

advent.print_answer(1, position)


start, step, size = 0, 1, 119315717514047
target_position = 2020
repetitions = 101741582076661

start, step = transform(start, step, size, moves)
start, step = repeat(start, step, size, repetitions)
card = (start + step * target_position) % size

advent.print_answer(2, card)
