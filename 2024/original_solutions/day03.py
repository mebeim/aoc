#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 3)

fin = advent.get_input()
data = fin.read()

ans1 = ans2 = 0

for a, b in re.findall(r'mul\((\d+),(\d+)\)', data):
	a = int(a)
	b = int(b)
	ans1 += a * b

advent.print_answer(1, ans1)

enabled = True

for m in re.findall(r'mul\((\d+),(\d+)\)|(don\'t\(\))|(do\(\))', data):
	if m[2] == 'don\'t()':
		enabled = False
		continue
	elif m[3] == 'do()':
		enabled = True
		continue

	if enabled:
		a, b = m[:2]
		a = int(a)
		b = int(b)
		ans2 += a * b

advent.print_answer(2, ans2)
