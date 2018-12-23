#!/usr/bin/env python3

import re
import sys
import copy
import heapq
import string
import time
import atexit
from collections import defaultdict, deque, namedtuple, Counter
from functools import lru_cache

def seconds_to_most_relevant_unit(s):
	s *= 1e6
	if s < 1000: return '{:.3f}µs'.format(s)

	s /= 1000
	if s < 1000: return '{:.3f}ms'.format(s)

	s /= 1000
	if s < 60: return '{:.3f}s'.format(s)

	s /= 60
	return '{:d}m {:.3f}s'.format(int(s), s/60%60)

#############################################################

def log(s, *a):
	sys.stderr.write(s.format(*a))
	sys.stderr.flush()

def rlog(recursion_depth):
	def fn(s, *a):
		log(' |' * recursion_depth + ' ' + s, *a)

	return fn

def dump_list(lst, fmt='{}'):
	for el in lst:
		log(fmt + '\n', el)

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

def timer_start(name=sys.argv[0]):
	now_wall, now_cpu = time.time(), time.clock()
	GLOBAL_TIMERS[name] = (now_wall, now_cpu, now_wall, now_cpu, 1)

def timer_stop(name=sys.argv[0]):
	now_wall, now_cpu = time.time(), time.clock()
	prev_wall, prev_cpu, *_ = GLOBAL_TIMERS.pop(name)

	dt_wall = seconds_to_most_relevant_unit(now_wall - prev_wall)
	dt_cpu  = seconds_to_most_relevant_unit(now_cpu  - prev_cpu )

	log('Timer {}: {} wall, {} CPU\n'.format(name, dt_wall, dt_cpu))

def timer_lap(name=sys.argv[0]):
	now_wall, now_cpu = time.time(), time.clock()
	*x, prev_wall, prev_cpu, lap = GLOBAL_TIMERS[name]

	dt_wall = seconds_to_most_relevant_unit(now_wall - prev_wall)
	dt_cpu  = seconds_to_most_relevant_unit(now_cpu  - prev_cpu )

	log('Timer {} lap #{}: {} wall, {} CPU\n'.format(name, lap, dt_wall, dt_cpu))

	GLOBAL_TIMERS[name] = (*x, time.time(), time.clock(), lap + 1)

def timer_stop_all():
	now_wall, now_cpu = time.time(), time.clock()

	while GLOBAL_TIMERS:
		k, v = GLOBAL_TIMERS.popitem()
		prev_wall, prev_cpu, *_ = v
		dt_wall = seconds_to_most_relevant_unit(now_wall - prev_wall)
		dt_cpu  = seconds_to_most_relevant_unit(now_cpu  - prev_cpu )

		log('Timer {}: {} wall, {} CPU\n'.format(k, dt_wall, dt_cpu))

def get_ints(file, use_regexp=False, regexp=r'-?\d+', as_tuple=False):
	kind = tuple if as_tuple else list
	exp  = re.compile(regexp)

	if use_regexp:
		return kind(map(int, exp.findall(file.read())))
	return kind(map(int, file.read().split()))

def get_int_matrix(file, use_regexp=False, regexp=r'-?\d+', as_tuples=False):
	kind = tuple if as_tuples else list
	exp  = re.compile(regexp)

	if use_regexp:
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

########################################################

GLOBAL_TIMERS = {}

########################################################

from platform import python_implementation

if python_implementation() == 'CPython':
	import blist
	import networkx as nx

atexit.register(timer_stop_all)
