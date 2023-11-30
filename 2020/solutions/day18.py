#!/usr/bin/env python3

import sys
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

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

exprs = tuple(map(tokenize, fin))
total = sum(map(evaluate, map(deque, exprs)))
print('Part 1:', total)

total = sum(map(partial(evaluate, plus_precedence=True), map(deque, exprs)))
print('Part 2:', total)
