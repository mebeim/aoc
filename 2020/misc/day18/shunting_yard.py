#!/usr/bin/env python3
#
# Alternative "textbook" general solution using the Shunting-yard algorithm.
#

from re import findall
from collections import deque
from operator import add, mul
from functools import partial

class Op:
	__slots__ = ('op', 'precedence')

	def __init__(self, op=None, precedence=0):
		self.op = op
		self.precedence = precedence

	def __call__(self, a, b):
		return self.op(a, b)

	def __gt__(self, other):
		return self.precedence >= other.precedence

	# NOTE: the above means infix_to_rpl will treat this as a left associative operator.
	# To also support right associativity (with a boolean rightassoc attribute):
	# def __gt__(self, other):
	# 	if self.rightassoc:
	# 		return self.precedence > other.precedence
	# 	else:
	# 		return self.precedence >= other.precedence

	def __repr__(self):
		return '+' if self.op is add else '*'

def tokenize(expr):
	return deque(findall(r'[0-9]+|[+*()]', expr))

def infix_to_rpl(tokens, opmap):
	'''Simplified shunting-yard algorithm (no function support).'''
	ops = deque() # operator stack

	while tokens:
		tok = tokens.popleft()

		if all(c.isdigit() for c in tok):
			yield int(tok)
		elif tok == '(':
			ops.append(tok)
		elif tok == ')':
			while ops[-1] != '(':
				yield ops.pop()
			ops.pop()
		else:
			op = opmap[tok]
			while ops and ops[-1] != '(' and ops[-1] > op:
				yield ops.pop()
			ops.append(op)

	yield from reversed(ops)

def evaluate(expr, opmap):
	toks  = tokenize(expr)
	rpl   = infix_to_rpl(toks, opmap)
	stack = deque()

	for v in rpl:
		if isinstance(v, Op):
			b, a = stack.pop(), stack.pop()
			stack.append(v(a, b))
		else:
			stack.append(v)

	return stack.pop()


fin = open('input.txt')
exprs = fin.readlines()

opmap = {'+': Op(add), '*': Op(mul)} # same precedence
total = sum(map(partial(evaluate, opmap=opmap), exprs))
print('Part 1:', total)


opmap = {'+': Op(add, 2), '*': Op(mul, 1)} # + has higher precendence than *
total = sum(map(partial(evaluate, opmap=opmap), exprs))
print('Part 2:', total)
