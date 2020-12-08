#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 8)
fin = advent.get_input()

timer_start()
lines = get_lines(fin)

prog = []
for l in lines:
	op, n = l.split()
	n = int(n)

	prog.append((op, n))

pc = 0
acc = 0
seen = set()

while 1:
	if pc in seen:
		break
	seen.add(pc)

	op, arg = prog[pc]
	print(pc, op, arg)

	if op == 'acc':
		acc += arg
		pc += 1
	elif op == 'nop':
		pc += 1
	elif op == 'jmp':
		pc = pc + arg

advent.submit_answer(1, acc)

i = 0
while i < len(prog):
	# print(i)
	prog2 = prog[:]
	op, arg = prog2[i]

	if op == 'nop':
		prog2[i] = ('jmp', arg)
	elif op == 'jmp':
		prog2[i] = ('nop', arg)

	done = 0
	acc = 0
	seen = set()
	pc = 0

	while 1:
		if pc in seen:
			break
		seen.add(pc)

		op, arg = prog2[pc]
		# print(pc, op, arg)

		if op == 'acc':
			acc += arg
			pc += 1
		elif op == 'nop':
			pc += 1
		elif op == 'jmp':
			pc = pc + arg

		if pc > len(prog2):
			break
		elif pc == len(prog2):
			done = 1
			break

	if done:
		break
	i += 1

# 1210 wrong
advent.submit_answer(2, acc)
