#!/usr/bin/env python3

from utils.all import *

advent.setup(2022, 5)
fin = advent.get_input()

# NOTE: Will only work with my input because I did not bother parsing the stacks
#       and copy-pasted them by hand instead.
stacks = [
	0,
	list('WBGZRDCV'),
	list('VTSBCFWG'),
	list('WNSBC'),
	list('PCVJNMGQ'),
	list('BHDFLST'),
	list('NMWTVJ'),
	list('GTSCLFP'),
	list('ZDB'),
	list('WZNM'),
]

for line in fin:
	if line == '\n':
		break

for line in fin:
	a, b, c = map(int, re.findall(r'\d+', line))

	for _ in range(a):
		x = stacks[b].pop(0)
		stacks[c].insert(0, x)

ans = ''.join(x[0] for x in stacks[1:])
advent.print_answer(1, ans)


stacks = [
	0,
	'WBGZRDCV',
	'VTSBCFWG',
	'WNSBC',
	'PCVJNMGQ',
	'BHDFLST',
	'NMWTVJ',
	'GTSCLFP',
	'ZDB',
	'WZNM',
]

fin.seek(0)
for line in fin:
	if line == '\n':
		break

for line in fin:
	a, b, c = map(int, re.findall(r'\d+', line))

	x = stacks[b][:a]
	stacks[c] = x + stacks[c]
	stacks[b] = stacks[b][a:]

ans = ''.join(x[0] for x in stacks[1:])
advent.print_answer(2, ans)
