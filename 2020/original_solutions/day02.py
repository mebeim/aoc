#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 2)
fin = advent.get_input()
eprint(*fin, sep=''); fin.seek(0, 0)
timer_start()

lines = get_lines(fin)

n = 0
for l in lines:
	p = l.split(' ')

	mmin, mmax = map(int, p[0].split('-'))
	let = p[1][0]
	pwd = p[2]

	if mmin <= pwd.count(let) <= mmax:
		n += 1

advent.submit_answer(1, n)

n = 0
for l in lines:
	p = l.split(' ')

	mmin, mmax = map(int, p[0].split('-'))
	let = p[1][0]
	pwd = p[2]

	if pwd[mmin-1] == let and pwd[mmax-1] != let or pwd[mmin-1] != let and pwd[mmax-1] == let:
		n += 1

advent.submit_answer(2, n)
