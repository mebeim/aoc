#!/usr/bin/env python3

from utils import advent
from functools import reduce
from itertools import permutations

def is_number(p):
	return type(p) is int

def add_to_leftmost(pair, num):
	if is_number(pair):
		return pair + num
	return (add_to_leftmost(pair[0], num), pair[1])

def add_to_rightmost(pair, num):
	if is_number(pair):
		return pair + num
	return (pair[0], add_to_rightmost(pair[1], num))

def explode(pair, depth=0):
	if is_number(pair):
		return None, pair, None, False

	left, right = pair

	if depth == 4:
		return left, 0, right, True

	left_num, left, right_num, did_explode = explode(left, depth + 1)

	if did_explode:
		if right_num is None:
			return left_num, (left, right), None, True
		return left_num, (left, add_to_leftmost(right, right_num)), None, True

	left_num, right, right_num, did_explode = explode(right, depth + 1)

	if did_explode:
		if left_num is None:
			return None, (left, right), right_num, True
		return None, (add_to_rightmost(left, left_num), right), right_num, True

	return None, pair, None, False

def split(pair):
	if is_number(pair):
		if pair < 10:
			return pair, False

		left = pair // 2
		return (left, pair - left), True

	left, right = pair
	left, did_split = split(left)

	if not did_split:
		right, did_split = split(right)

	return (left, right), did_split

def simplify(pair):
	keep_going = True

	while keep_going:
		_, pair, _, keep_going = explode(pair)
		if keep_going:
			continue

		pair, keep_going = split(pair)

	return pair

def add(a, b):
	return simplify((a, b))

def magnitude(pair):
	if is_number(pair):
		return pair
	return 3 * magnitude(pair[0]) + 2 * magnitude(pair[0])


advent.setup(2021, 18)
fin = advent.get_input()

trans = str.maketrans('[]', '()')
pairs = tuple(eval(line.translate(trans) for line in fin))
mag   = magnitude(reduce(add, pairs))
advent.print_answer(1, mag)


best = max(map(magnitude, map(simplify, permutations(pairs, 2))))
advent.print_answer(2, best)
