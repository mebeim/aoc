#!/usr/bin/env python3

from utils import advent
from re import findall
from collections import deque
from operator import add, mul
from functools import partial

def tokenize(expr):
	return findall(r'\d+|[+*()]', expr)

def evaluate(tokens, plus_precedence=False):
	multiplier = 1
	accumulator = 0
	op = add

	while tokens:
		tok = tokens.popleft()

		if tok.isdigit():
			val = int(tok) * multiplier
			accumulator = op(accumulator, val)
		elif tok == '+':
			op = add
		elif tok == '*':
			if plus_precedence:
				multiplier  = accumulator
				accumulator = 0
			else:
				op = mul
		elif tok == '(':
			val = evaluate(tokens, plus_precedence) * multiplier
			accumulator = op(accumulator, val)
		else: # ')'
			break

	return accumulator

advent.setup(2020, 18)
fin = advent.get_input()

exprs = tuple(map(tokenize, fin))
total = sum(map(evaluate, map(deque, exprs)))
advent.print_answer(1, total)

total = sum(map(partial(evaluate, plus_precedence=True), map(deque, exprs)))
advent.print_answer(2, total)
