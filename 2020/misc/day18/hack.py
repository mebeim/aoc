#!/usr/bin/env python3
#
# Alternative "hacky" solution abusing Python's object model.
#

import re
import sys

class K:
	__slots__ = ('value')

	def __init__(self, value):
		self.value = value

	def __sub__(self, other):
		return K(self.value + other.value)

	def __add__(self, other):
		return K(self.value * other.value)

	def __mul__(self, other):
		return K(self.value + other.value)


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

with fin:
	exprs = fin.read().splitlines()

table1 = str.maketrans('+*', '-+')
table2 = str.maketrans('+*', '*+')
regexp = re.compile(r'(\d+)')
total1 = 0
total2 = 0

for expr in exprs:
	expr = regexp.sub(r'K(\1)', expr)

	expr1 = expr.translate(table1)
	total1 += eval(expr1).value

	expr2 = expr.translate(table2)
	total2 += eval(expr2).value

print('Part 1:', total1)
print('Part 2:', total2)
