#!/usr/bin/env python3

from utils.all import *

def conv(l):
	n = 0
	power = 1

	for c in l[::-1]:
		if c == '-':
			v = -1
		elif c == '=':
			v = -2
		else:
			v = ord(c) - ord('0')

		n += v * power
		power *= 5

	return n

advent.setup(2022, 25)

fin = advent.get_input()
lines = read_lines(fin)

total = 0
for l in lines:
	l = l.strip()
	total += conv(l)

digits = 1
while 5 ** digits < total:
	digits += 1

num = ['2'] * digits

for i in range(len(num)):
	for d in '=-012':
		num[i] = d
		# eprint(''.join(num), conv(num), total)
		if conv(num) >= total:
			break

ans = ''.join(num)

advent.print_answer(1, ans)
