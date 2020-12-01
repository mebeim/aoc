#!/usr/bin/env python3

from utils.all import *
from operator import add, mul
import sys

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

def run(prog, input_id):
	pc = 0
	lastout = None

	while prog[pc] != 99:
		op = prog[pc] % 10
		modes = '000' + str(prog[pc])[:-2]
		derefa = modes[-1] == '0'
		derefb = modes[-2] == '0'

		if op in (1, 2):
			opp = add if op == 1 else mul
			a, b, c = prog[pc + 1:pc + 4]

			# log('{:30} | {} {:-8d}{} {:-8d}{} {:-8d} \n',
			# 	repr(prog[pc:pc + 4]),
			# 	'SUM' if opp == add else 'MUL',
			# 	a, '*' if derefa else ' ',
			# 	b, '*' if derefb else ' ',
			# 	c
			# )

			if derefa: a = prog[a]
			if derefb: b = prog[b]

			prog[c] = opp(a, b)

			pc += 4
		elif op in (3, 4):
			a = prog[pc + 1]

			if op == 3:
				# log('{:30} | IN  {:-8d}\n',  repr(prog[pc:pc+2]), a)

				# provide id as only input
				prog[a] = input_id
			else:
				# log('{:30} | OUT {:-8d}{}\n', repr(prog[pc:pc+2])+modes, a, '*' if derefa else '')

				if derefa:
					a = prog[a]

				# log('-'*80 + ' OUTPUT: {}\n', a)
				lastout = a

			pc += 2
		elif op == 5:
			a, b = prog[pc + 1:pc + 3]
			if derefa: a = prog[a]
			if derefb: b = prog[b]

			# log('{:30} | JNZ {:-8d}{} {:-8d}{}\n',
			# 	repr(prog[pc:pc + 3]),
			# 	a, '*' if derefa else ' ',
			# 	b, '*' if derefb else ' ',
			# )

			if a != 0: pc = b
			else: pc += 3
		elif op == 6:
			a, b = prog[pc + 1:pc + 3]
			# log('{:30} | JZ  {:-8d}{} {:-8d}{}\n',
			# 	repr(prog[pc:pc + 3]),
			# 	a, '*' if derefa else ' ',
			# 	b, '*' if derefb else ' ',
			# )

			if derefa: a = prog[a]
			if derefb: b = prog[b]

			if a == 0: pc = b
			else: pc += 3
		elif op == 7:
			a, b, c = prog[pc + 1:pc + 4]
			if derefa: a = prog[a]
			if derefb: b = prog[b]
			prog[c] = 1 if a < b else 0
			pc += 4
		elif op == 8:
			a, b, c = prog[pc + 1:pc + 4]
			if derefa: a = prog[a]
			if derefb: b = prog[b]
			prog[c] = 1 if a == b else 0
			pc += 4
		else:
			eprint('INVALID op at pc =', pc, 'value =', op)
			sys.exit(1)

	return lastout


program = list(map(int, fin.read().split(',')))

result1 = run(program[:], 1)

# 225 wrong
# 2680 wrong
# -50799651125152 wrong LOL
advent.submit_answer(1, result1)

result2 = run(program[:], 5)

advent.submit_answer(2, result2)
