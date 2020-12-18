#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 18)
fin = advent.get_input()
timer_start()

def precedence(op):
	if op in '+*':
		return 1
	return 0

def applyOp(a, b, op):
	if op == '+': return a + b
	if op == '-': return a - b
	if op == '*': return a * b
	if op == '/': return a // b

# Well... what can I say...
# https://www.geeksforgeeks.org/expression-evaluation/
def evaluate(tokens):
	values = []
	ops = []
	i = 0

	while i < len(tokens):
		if tokens[i] == ' ':
			i += 1
			continue
		elif tokens[i] == '(':
			ops.append(tokens[i])
		elif tokens[i].isdigit():
			val = 0
			while (i < len(tokens) and
				tokens[i].isdigit()):

				val = (val * 10) + int(tokens[i])
				i += 1

			values.append(val)
			i-=1
		elif tokens[i] == ')':

			while len(ops) != 0 and ops[-1] != '(':
				val2 = values.pop()
				val1 = values.pop()
				op = ops.pop()
				values.append(applyOp(val1, val2, op))
			ops.pop()
		else:
			while (len(ops) != 0 and
				precedence(ops[-1]) >=
				precedence(tokens[i])):
				val2 = values.pop()
				val1 = values.pop()
				op = ops.pop()
				values.append(applyOp(val1, val2, op))

			ops.append(tokens[i])

		i += 1

	while len(ops) != 0:
		val2 = values.pop()
		val1 = values.pop()
		op = ops.pop()
		values.append(applyOp(val1, val2, op))

	return values[-1]

lines = get_lines(fin)

tot = 0
for l in lines:
	res = evaluate(l.rstrip())
	# print(l, res)
	tot += res

# 44960197700 wrong
# 70518821989947 wrong
advent.print_answer(1, tot)


def precedence(op):
	if op == '+':
		return 2
	if op == '*':
		return 1
	return 0

tot = 0
for l in lines:
	res = evaluate(l.rstrip())
	# print(l, res)
	tot += res

advent.print_answer(2, tot)

