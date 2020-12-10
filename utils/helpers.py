__all__ = [
	'log', 'rlog', 'eprint', 'wait',
	'dump_iterable', 'dump_dict', 'dump_char_matrix',
	'get_ints', 'get_int_matrix', 'get_lines', 'get_char_matrix'
]

import sys
import re
from functools import wraps

def log(s, *a):
	'''Log a string to standard error after formatting it with any additionally
	provided argument.
	'''
	sys.stderr.write(s.format(*a))
	sys.stderr.flush()

def rlog(recursion_depth):
	'''Create a logging function that behaves like log(), but adds
	recursion_depth levels of indentation to each logged string.

	Useful for debugging recursive function calls, for example:

		def fib(n, depth=0):
			log = rlog(depth)
			log('n={}\n', n)
			if n == 0 or n == 1:
				return n
			return n + fib(n - 1, depth + 1) + fib(n - 2, depth + 1)

		>>> fib(3)
		n=3
		| n=2
		| | n=1
		| | n=0
		| n=1
	'''
	@wraps(log)
	def fn(s, *a):
		log(' |' * recursion_depth + ' ' + s, *a)

	return fn

def eprint(*a, **kwa):
	'''Wrapper for print() that prints on standard error.'''
	print(*a, **kwa, file=sys.stderr)

def wait(msg):
	'''Wait for user interaction by printing a message to standard error and
	waiting for input.
	'''
	eprint(msg, end=' ')
	input()

def dump_iterable(iterable, fmt='{:d}: {!r}'):
	'''Dump index and values of an iterable using the specified format string to
	standard error.
	'''
	for i, item in enumerate(iterable):
		log(fmt + '\n', i, item)

def dump_dict(dct, fmt='{}: {!r}'):
	'''Dump keys and values of a dictionary using the specified format string to
	standard error.
	'''
	for k, v in dct.items():
		log(fmt + '\n', k, v)

def dump_char_matrix(mat, transpose=False):
	'''Dump the contents of a matrix of characters (e.g. list of string or list
	of list of single-char strings) to standard error.

	If transpose=True, print the transposed matrix.
	'''
	if transpose:
		for j in range(len(mat[0])):
			for i in range(len(mat)):
				sys.stderr.write(mat[i][j])
			sys.stderr.write('\n')
	else:
		for i in range(len(mat)):
			for j in range(len(mat[i])):
				sys.stderr.write(mat[i][j])
			sys.stderr.write('\n')

	sys.stderr.flush()

def get_ints(file, use_regexp=False, regexp=r'-?\d+', as_tuple=False):
	'''Parse file containing whitespace delimited integers into a list of
	integers.

	If use_regexp=True, parse the entire file using regexp to extract integers.
	Returns a list of list by default, or a tuple of tuple if as_tuple=True.
	'''
	kind = tuple if as_tuple else list

	if use_regexp:
		exp = re.compile(regexp)
		return kind(map(int, exp.findall(file.read())))
	return kind(map(int, file.read().split()))

def get_int_matrix(file, use_regexp=False, regexp=r'-?\d+', as_tuples=False):
	'''Parse file containing lines of whitespace delimited decimal integers into
	a matrix of integers, one line = one row.

	If use_regexp=True, uses regexp to parse each line to extract integers.
	Returns a list of list by default, or a tuple of tuple if as_tuples=True.
	'''
	kind = tuple if as_tuples else list

	if use_regexp:
		exp = re.compile(regexp)
		return kind(kind(map(int, exp.findall(l))) for l in file)
	return kind(kind(map(int, l.split())) for l in file)

def get_lines(file, rstrip=True, lstrip=True, as_tuple=False):
	'''Read file into a list (or tuple) of lines

	Strips lines on both ends by default unless rstrip=False or lstrip=False.
	Returns a list of strings by default, or a tuple if as_tuple=True.
	'''
	kind  = tuple if as_tuple else list
	lines = map(lambda l: l.rstrip('\n'), file)

	if rstrip and lstrip:
		return kind(map(str.strip, lines))
	if rstrip:
		return kind(map(str.rstrip, lines))
	if lstrip:
		return kind(map(str.lstrip, lines))
	return kind(lines)

def get_char_matrix(file, rstrip=True, lstrip=True, as_tuples=False):
	'''Read file into a matrix of characters.

	Strips lines on both ends by default unless rstrip=False or lstrip=False.
	Returns a list of list by default, or a tuple of tuple if as_tuples=True.
	'''
	kind  = tuple if as_tuples else list
	lines = map(lambda l: l.rstrip('\n'), file)

	if rstrip and lstrip:
		return kind(kind(l.strip()) for l in lines)
	if rstrip:
		return kind(kind(l.rstrip()) for l in lines)
	if lstrip:
		return kind(kind(l.lstrip()) for l in lines)
	return kind(map(kind, lines))
