#!/usr/bin/env python3

from utils.all import *

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

lines = get_lines(fin)

import re
from math import gcd
rexp = re.compile(r'-?\d+')

DEAL_STEP, DEAL_NEW, CUT = 0,1,2

def build_moves(length):
	moves = []
	for l in lines:
		if 'deal with' in l:
			n = int(rexp.findall(l)[0])
			moves.append((DEAL_STEP, n))
		elif 'deal into' in l:
			moves.append((DEAL_NEW, 0))
		elif 'cut' in l:
			n = int(rexp.findall(l)[0])
			if n < 0:
				n += length
			moves.append((CUT, n))

	return moves

def shuffle(i, length, moves):
	for move, n in moves:
		if move == DEAL_NEW:
			i = length - i - 1
		elif move == DEAL_STEP:
			i = (i * n) % length
		else:
			if i >= n:
				i -= n
			else:
				i = length - n + i

	return i

def shuffle2(a, b, length, moves):
	for move, n in moves:
		if move == DEAL_NEW:
			a = (-1 * a) % length
			b = (b + a) % length
		elif move == DEAL_STEP:
			a = (a * pow(n, length-2, length)) % length
		else:
			b = (a * n + b) % length

	return a, b

card   = 2019
length = 10007
moves = build_moves(length)

card = shuffle(card, length, moves)
advent.submit_answer(1, card)


card = 2020
length = 119315717514047
repetitions = 101741582076661
moves = build_moves(length)

a = 1
b = 0

a, b = shuffle2(a, b, length, moves)
# print(a, b)

A = pow(a, repetitions, length)
S = (1 - A) * pow(1 - a, length-2, length)
B = (b * S) % length
# print(A, B)

final = (A * card + B) % length

# 56945290822617 wrong
# 106845040107460 wrong
advent.submit_answer(2, final)
