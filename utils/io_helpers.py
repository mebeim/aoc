__all__ = [
	'log', 'rlog', 'eprint', 'reprint', 'wait',
	'dump_iterable', 'dump_dict', 'dump_char_matrix', 'dump_sparse_matrix',
	'extract_ints', 'read_lines', 'read_ints',
	'read_int_matrix', 'read_char_matrix', 'read_digit_matrix'
]


import sys
import re
from collections.abc import Callable, Collection, Iterable, Sequence
from functools import wraps
from typing import Any, TextIO, Union


StrOrBytes = Union[str,bytes]


def log(s: str, *a: Any):
	'''Log a string to standard error after formatting it with any additionally
	provided argument.
	'''
	sys.stderr.write(s.format(*a))
	sys.stderr.flush()

def rlog(recursion_depth: int) -> Callable[...,None]:
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

def reprint(recursion_depth: int):
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

def wait(msg: str='Press [ENTER] to continue...'):
	'''Wait for user interaction by printing a message to standard error and
	waiting for input.
	'''
	eprint(msg, end=' ')

	try:
		input()
	except KeyboardInterrupt:
		log(" keyboard interrupt, exiting...\n")
		sys.exit(0)

def dump_iterable(iterable: Iterable, fmt: str='{:d}: {!r}'):
	'''Dump index and values of an iterable using the specified format string to
	standard error.
	'''
	for i, item in enumerate(iterable):
		log(fmt + '\n', i, item)

def dump_dict(dct: dict[Any,Any], fmt: str='{}: {!r}'):
	'''Dump keys and values of a dictionary using the specified format string to
	standard error.
	'''
	for k, v in dct.items():
		log(fmt + '\n', k, v)

def dump_char_matrix(mat: Sequence[Sequence[str]], transpose: bool=False):
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

def dump_sparse_matrix(mat: Union[set[tuple[int,int]],dict[tuple[int,int],str]],
		chars: str='# ', transpose: bool=False, header: bool=False):
	'''Dump the contents of a sparse matrix (e.g. a set or a dict, where the key
	is the coordinates of a cell in the matrix) to standard error.

	For a dict, values in the dict are printed as is for present coordinates,
	while chars[1] is printed for non-present ones. For a set, char[0] is
	printed for present coordinates and char[1] for non-present ones.

	If transpose=True, print the transposed matrix.

	If header=True, print top-left and bottom-right coordinates represenitng the
	extreme points of the bounding box of the sparse matrix.
	'''
	if type(chars) is not str and len(chars) != 2:
		raise ValueError('chars must be a two-character string')

	minr, maxr = min(r for r, _ in mat), max(r for r, _ in mat)
	minc, maxc = min(c for _, c in mat), max(c for _, c in mat)

	if isinstance(mat, (set, frozenset)):
		value_at = lambda x: chars[x not in mat]
	else:
		value_at = lambda x: mat.get(x, chars[1])

	if transpose:
		if header:
			log('TRANSPOSED sparse matrix from ({}, {}) to ({}, {}):\n',
				minc, minr, maxc, maxr)

		for c in range(minc, maxc + 1):
			for r in range(minr, maxr + 1):
				sys.stderr.write(value_at((r, c)))
			sys.stderr.write('\n')
	else:
		if header:
			log('Sparse matrix from ({}, {}) to ({}, {}):\n',
				minr, minc, maxr, maxc)

		for r in range(minr, maxr + 1):
			for c in range(minc, maxc + 1):
				sys.stderr.write(value_at((r, c)))
			sys.stderr.write('\n')

def extract_ints(str_or_bytes: StrOrBytes, container: type[Collection]=list,
		negatives: bool=True) -> Collection[int]:
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

def read_lines(file: TextIO, rstrip: bool=True, lstrip: bool=True,
		container: type[Collection]=list) -> Collection[str]:
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

def read_ints(file: TextIO, container: type[Collection]=list,
		negatives: bool=True) -> Collection[int]:
	'''Parse file containing integers into a list of integers.

	With negative=False, discard any leading hypen, effectively extracting
	positive integer values even when perceded by hypens.

	The container= class is instantiated to hold the ints.
	'''
	return extract_ints(file.read(), container, negatives)

def read_int_matrix(file: TextIO, container: type[Collection]=list,
		outer_container: type[Collection]=list, negatives: bool=True) \
		-> Collection[Collection[int]]:
	'''Parse file containing lines containing integers into a list of lists of
	int. Integers are extracted using a regular expression.

	With negative=False, discard any leading hypen, effectively extracting
	positive integer values even when preceeded by hypens.

	The container= class is instantiated to hold the ints in each line.
	The outer_container= class is instantiate to hold the lines.
	'''
	return outer_container(extract_ints(l, container, negatives) for l in file)

def read_char_matrix(file: TextIO, rstrip: bool=False, lstrip: bool=False,
		container: type[Collection]=list,
		outer_container: type[Collection]=list) -> Collection[Collection[str]]:
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

def read_digit_matrix(file: TextIO, container: type[Collection]=list,
		outer_container: type[Collection]=list) -> Collection[Collection[int]]:
	'''Parse file containing lines containing *digits* into a list of lists of
	int. Each digit is converted to integer.

	The container= class is instantiated to hold the ints in each line.
	The outer_container= class is instantiate to hold the lines.
	'''
	return outer_container(container(map(int, line.strip())) for line in file)
