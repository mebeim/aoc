__all__ = [
	'log', 'rlog', 'eprint', 'reprint', 'wait',
	'dump_iterable', 'dump_dict', 'dump_char_matrix', 'dump_sparse_matrix',
	'extract_ints', 'read_lines', 'read_ints',
	'read_int_matrix', 'read_char_matrix', 'read_digit_matrix',
	'autorange'
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
			log('fib({})\n', n, is_header=True)

			if n == 0 or n == 1:
				log('{}\n', n, last=1)
				return n

			log('hello\n')

			res = n + fib(n - 1, depth + 1) + fib(n - 2, depth + 1)
			log('{}\n', res, last=1)

			return res

		>>> fib(3)
		┌ fib(3)
		│ hello
		│ ┌ fib(2)
		│ │ hello
		│ │ ┌ fib(1)
		│ │ └> 1
		│ │ ┌ fib(0)
		│ │ └> 0
		│ └> 3
		│ ┌ fib(1)
		│ └> 1
		└> 7
	'''
	@wraps(log)
	def fn(s, *a, is_header=False, is_retval=False):
		pre = ' │' * recursion_depth
		pre += ' ┌' if is_header else ' └>' if is_retval else ' │'
		log(pre + ' ' + s, *a)

	return fn

def eprint(*a, **kwa):
	'''Wrapper for print() that prints on standard error.'''
	print(*a, **kwa, file=sys.stderr)

def reprint(recursion_depth):
	'''Create a printing function that behaves like eprint(), but adds
	recursion_depth levels of indentation to each logged string.

	Useful for debugging recursive function calls, for example:

		def fib(n, depth=0):
			ep = reprint(depth)
			ep('n =', n, is_header=1)

			if n == 0 or n == 1:
				ep(n, is_retval=1)
				return n

			ep('hello')
			res = n + fib(n - 1, depth + 1) + fib(n - 2, depth + 1)
			ep(res, is_retval=1)

			return res

		>>> fib(3)
		┌ n = 3
		│ hello
		│ ┌ n = 2
		│ │ hello
		│ │ ┌ n = 1
		│ │ └> 1
		│ │ ┌ n = 0
		│ │ └> 0
		│ └> 3
		│ ┌ n = 1
		│ └> 1
		└> 7
	'''
	@wraps(log)
	def fn(*a, is_header=False, is_retval=False, **kwa):
		pre = ' │' * recursion_depth
		pre += ' ┌' if is_header else ' └>' if is_retval else ' │'
		eprint(pre, end=' ')
		eprint(*a, **kwa)

	return fn

def wait(msg='Press [ENTER] to continue...'):
	'''Wait for user interaction by printing a message to standard error and
	waiting for input.
	'''
	eprint(msg, end=' ')

	try:
		input()
	except KeyboardInterrupt:
		log(" keyboard interrupt, exiting...\n")
		sys.exit(0)

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

def dump_sparse_matrix(mat, chars='# ', transpose=False, header=False):
	'''Dump the contents of a sparse matrix (e.g. a set or a dict, where the key
	is the coordinates of a cell in the matrix) to standard error.

	The TWO chars are used to represent coordinates present (first char) or not
	present (second char) in the matrix. For a dict, values in the dict are used
	for coordinates that are present instead.

	If transpose=True, print the transposed matrix.

	If header=True, print top-left and bottom-right coordinates represenitng the
	extreme points of the bounding box of the sparse matrix.
	'''
	if type(chars) is not str and len(chars) != 2:
		raise ValueError('chars must be a two-character string')

	minr, maxr = min(r for r, _ in mat), max(r for r, _ in mat)
	minc, maxc = min(c for _, c in mat), max(c for _, c in mat)

	if type(mat) is set:
		char_at = lambda x: chars[x not in mat]
	else:
		char_at = lambda x: mat.get(x, chars[1])

	if header:
		fmt = ('TRANSPOSED s' if transpose else 'S') + 'parse matrix from ({}, {}) to ({}, {}):\n'
		log(fmt, minr, minc, maxr, maxc)

	if transpose:
		for c in range(minc, maxc + 1):
			for r in range(minr, maxr + 1):
				sys.stderr.write(char_at((r, c)))
			sys.stderr.write('\n')
	else:
		for r in range(minr, maxr + 1):
			for c in range(minc, maxc + 1):
				sys.stderr.write(char_at((r, c)))
			sys.stderr.write('\n')

def extract_ints(str_or_bytes, container=list, negatives=True):
	'''Extract integers within a string or a bytes object using a regular
	expression and return a list of int.

	With negative=False, discard any leading hypen, effectively extracting
	positive integer values even when perceded by hypens.

	The container= class is instantiated to hold the ints.
	'''
	exp = r'-?\d+' if negatives else r'\d+'
	if isinstance(str_or_bytes, bytes):
		exp = exp.encode()
	return container(map(int, re.findall(exp, str_or_bytes)))

def read_lines(file, rstrip=True, lstrip=True, container=list):
	'''Read file into a list of lines. Strips lines on both ends by default
	unless rstrip=False or lstrip=False.

	The container= class is instantiated to hold the lines.
	'''
	lines = map(lambda l: l.rstrip('\n'), file)

	if rstrip and lstrip:
		return container(map(str.strip, lines))
	if rstrip:
		return container(map(str.rstrip, lines))
	if lstrip:
		return container(map(str.lstrip, lines))
	return container(lines)

def read_ints(file, container=list, negatives=True):
	'''Parse file containing integers into a list of integers.

	With negative=False, discard any leading hypen, effectively extracting
	positive integer values even when perceded by hypens.

	The container= class is instantiated to hold the ints.
	'''
	return extract_ints(file.read(), container, negatives)

def read_int_matrix(file, container=list, outer_container=list, negatives=True):
	'''Parse file containing lines containing integers into a list of lists of
	int. Integers are extracted using a regular expression.

	With negative=False, discard any leading hypen, effectively extracting
	positive integer values even when perceded by hypens.

	The container= class is instantiated to hold the ints in each line.
	The outer_container= class is instantiate to hold the lines.
	'''
	return outer_container(extract_ints(l, container, negatives) for l in file)

def read_char_matrix(file, rstrip=False, lstrip=False, container=list, outer_container=list):
	'''Read file into a matrix of characters (effectively a grid). Avoids
	stripping whitespace other than newlines, unless rstrip=True or lstrip=True.

	The container= class is instantiated to hold the characters in each line.
	The outer_container= class is instantiate to hold the lines.
	'''
	lines = map(lambda l: l.rstrip('\n'), file)

	if rstrip and lstrip:
		return outer_container(container(l.strip()) for l in lines)
	if rstrip:
		return outer_container(container(l.rstrip()) for l in lines)
	if lstrip:
		return outer_container(container(l.lstrip()) for l in lines)
	return outer_container(map(container, lines))

def read_digit_matrix(file, rstrip=False, lstrip=False, container=list, outer_container=list):
	'''Same as read_char_matrix, but each character is assumed to be an ASCII
	digit and is therefore transformed to int.
	'''
	mat = read_char_matrix(file, rstrip, lstrip)
	return outer_container(container(map(int, l)) for l in mat)

def autorange(start, end, step=1):
	'''Range from start to end (included) in steps of +/- step regardless if
	start > end or end > start.

	autorange(1, 3) -> 1, 2, 3
	autorange(3, 1) -> 3, 2, 1
	autorange(10, 1, 2) -> 10, 8, 6, 4, 2
	'''
	if start > end:
		yield from range(start, end - 1, -step)
	yield from range(start, end + 1, step)
