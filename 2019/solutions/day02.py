#!/usr/bin/env python3

from utils import advent
from operator import add, mul
from itertools import product

def run(prog, *inputs):
	prog[1:3] = inputs[:]
	pc = 0

	while prog[pc] != 99:
		op = add if prog[pc] == 1 else mul
		a, b, c = prog[pc + 1:pc + 4]
		prog[c] = op(prog[a], prog[b])
		pc += 4

	return prog[0]


advent.setup(2019, 2)
fin = advent.get_input()

program = list(map(int, fin.read().split(',')))
result = run(program[:], 12, 2)
advent.print_answer(1, result)


for noun, verb in product(range(100), range(100)):
	if run(program[:], noun, verb) == 19690720:
		break

answer = 100 * noun + verb
advent.print_answer(2, answer)
