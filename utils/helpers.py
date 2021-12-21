__all__ = [
	'log', 'rlog', 'eprint', 'wait',
	'dump_iterable', 'dump_dict', 'dump_char_matrix', 'dump_sparse_matrix',
	'get_ints', 'get_int_matrix', 'get_lines', 'get_char_matrix',
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
