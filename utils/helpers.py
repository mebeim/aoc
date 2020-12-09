import sys
import re

from functools import wraps

def log(s, *a):
	sys.stderr.write(s.format(*a))
	sys.stderr.flush()

def rlog(recursion_depth):
	@wraps(log)
	def fn(s, *a):
		log(' |' * recursion_depth + ' ' + s, *a)

	return fn

def eprint(*a, **kwa):
	print(*a, **kwa, file=sys.stderr)

def wait(msg):
	eprint(msg, end=' ')
	input()

def dump_iterable(iterable, fmt='{}'):
	for item in iterable:
		log(fmt + '\n', item)

def dump_dict(dct, fmt='{}: {}'):
	for k, v in dct.items():
		log(fmt + '\n', k, v)

def dump_char_matrix(mat, transpose=False):
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
	kind = tuple if as_tuple else list

	if use_regexp:
		exp = re.compile(regexp)
		return kind(map(int, exp.findall(file.read())))
	return kind(map(int, file.read().split()))

def get_int_matrix(file, use_regexp=False, regexp=r'-?\d+', as_tuples=False):
	kind = tuple if as_tuples else list

	if use_regexp:
		exp = re.compile(regexp)
		return kind(kind(map(int, exp.findall(l))) for l in file)
	return kind(kind(map(int, l.split())) for l in file)

def get_lines(file, rstrip=True, lstrip=True, as_tuple=False):
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
	kind  = tuple if as_tuples else list
	lines = map(lambda l: l.rstrip('\n'), file)

	if rstrip and lstrip:
		return kind(kind(l.strip()) for l in lines)
	if rstrip:
		return kind(kind(l.rstrip()) for l in lines)
	if lstrip:
		return kind(kind(l.lstrip()) for l in lines)
	return kind(map(kind, lines))

################################################################################

__all__ = [
	'log', 'rlog', 'eprint', 'wait',
	'dump_iterable', 'dump_dict', 'dump_char_matrix',
	'get_ints', 'get_int_matrix', 'get_lines', 'get_char_matrix'
]
