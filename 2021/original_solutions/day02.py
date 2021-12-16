#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 2)
fin = advent.get_input()
lines = get_lines(fin)

f = 0
d = 0
dd = 0
a = 0

for i, l in enumerate(lines):
	_, b = l.split()
	b = int(b)
	if l.startswith('down'):
		a += b
		d += b
	elif l.startswith('up'):
		a -= b
		d -= b
	else:
		f += b
		dd += a * b

ans = f * d

advent.print_answer(1, ans)
wait('Submit? ')
advent.submit_answer(1, ans)

ans = f * dd

advent.print_answer(2, ans)
wait('Submit? ')
advent.submit_answer(2, ans)
