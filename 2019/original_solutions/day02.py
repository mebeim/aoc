#!/usr/bin/env python3

from utils.all import *

from itertools import product

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

inp = get_ints(fin, True)

pc = 0
prog = inp[:]
prog[1] = 12
prog[2] = 2

while True:
	op = prog[pc]

	if op == 1:
		a = prog[pc + 1]
		b = prog[pc + 2]
		c = prog[pc + 3]
		prog[c] = prog[a] + prog[b]
		pc += 4
	elif op == 2:
		a = prog[pc + 1]
		b = prog[pc + 2]
		c = prog[pc + 3]
		prog[c] = prog[a] * prog[b]
		pc += 4
	elif op == 99:
		break
	else:
		eprint(pc, op)
		raise UnboundLocalError()

# 1690717 wrong answer
advent.submit_answer(1, prog[0])

pc = 0
prog = inp[:]

for x, y in product(range(100), range(100)):
	# eprint(x, y)
	pc = 0
	prog = inp[:]
	prog[1] = x
	prog[2] = y
	ok = False

	while True:
		op = prog[pc]

		if op == 1:
			a = prog[pc + 1]
			b = prog[pc + 2]
			c = prog[pc + 3]
			prog[c] = prog[a] + prog[b]
			pc += 4
		elif op == 2:
			a = prog[pc + 1]
			b = prog[pc + 2]
			c = prog[pc + 3]
			prog[c] = prog[a] * prog[b]
			pc += 4
		elif op == 99:
			break
		else:
			eprint(pc, op)
			raise UnboundLocalError()

	if prog[0] == 19690720:
		ok = True
		break

if ok:
	advent.submit_answer(2, 100 * x + y)
else:
	eprint('nope')
