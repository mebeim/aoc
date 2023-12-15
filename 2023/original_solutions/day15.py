#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 15)
DEBUG = 'debug' in map(str.lower, sys.argv)
fin = advent.get_input(mode='rb')

data = fin.read()
ans1 = ans2 = 0

def h(s):
	n = 0
	for c in s:
		n += c
		n *= 17
		n %= 256
	return n

for s in map(bytes.strip, data.split(b',')):
	ans1 += h(s)

advent.print_answer(1, ans1)


def bdel(a, lst: list):
	for i, (x, v) in enumerate(lst):
		if a == x:
			break
	else:
		return len(lst)

	lst.pop(i)
	return i

box = defaultdict(list)

def hm(s):
	if b'-' in s:
		a = s[:-1]
		k = h(a)
		bdel(a, box[k])

	if b'=' in s:
		a, b = s.split(b'=')
		b = int(b)
		k = h(a)
		i = bdel(a, box[k])
		box[k].insert(i, (a, b))

for s in map(bytes.strip, data.split(b',')):
	hm(s)

for i, lst in box.items():
	for j, (a, v) in enumerate(lst, 1):
		ans2 += (i + 1) * j * v

advent.print_answer(2, ans2)
