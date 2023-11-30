#!/usr/bin/env python3

import sys
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


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

program = list(map(int, fin.read().split(',')))
result = run(program[:], 12, 2)
print('Part 1:', result)


for noun, verb in product(range(100), range(100)):
	if run(program[:], noun, verb) == 19690720:
		break

answer = 100 * noun + verb
print('Part 2:', answer)
