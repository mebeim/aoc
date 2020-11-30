#!/usr/bin/env python3

from utils import advent

import re
import sys

advent.setup(2018, 19)
fin = advent.get_input()
# print(*fin)

##################################################

strings = list(map(str.strip, fin))

opcodes = {
	'addr': lambda r,a,b: r[a] + r[b],             #  0 addr
	'addi': lambda r,a,b: r[a] + b,                #  1 addi
	'mulr': lambda r,a,b: r[a] * r[b],             #  2 mulr
	'muli': lambda r,a,b: r[a] * b,                #  3 muli
	'banr': lambda r,a,b: r[a] & r[b],             #  4 banr
	'bani': lambda r,a,b: r[a] & b,                #  5 bani
	'borr': lambda r,a,b: r[a] | r[b],             #  6 borr
	'bori': lambda r,a,b: r[a] | b,                #  7 bori
	'setr': lambda r,a,b: r[a],                    #  8 setr
	'seti': lambda r,a,b: a,                       #  9 seti
	'gtir': lambda r,a,b: 1 if a > r[b] else 0,    # 10 gtir
	'gtri': lambda r,a,b: 1 if r[a] > b else 0,    # 11 gtri
	'gtrr': lambda r,a,b: 1 if r[a] > r[b] else 0, # 12 gtrr
	'eqir': lambda r,a,b: 1 if a == r[b] else 0,   # 13 eqir
	'eqri': lambda r,a,b: 1 if r[a] == b else 0,   # 14 eqri
	'eqrr': lambda r,a,b: 1 if r[a] == r[b] else 0 # 15 eqrr
}

ipreg = 3
prog = []

for s in strings[1:]:
	mnemonic, a, b, c = s.strip().split(' ')
	a, b, c = map(int, (a, b, c))
	prog.append((mnemonic, a, b, c))

eoc = len(prog)
print(eoc)

regs = [0, 0, 0, 0, 0, 0]
# regs[0] = 1

i = 0
while 0 <= regs[ipreg] < eoc:
	i += 1
	if i % 1000000 == 0:
		sys.stderr.write('{:12d} | ip: {:2d} {} | {}    \r'.format(i, regs[ipreg], prog[regs[ipreg]], regs))

	mnemonic, a, b, c = prog[regs[ipreg]]
	regs[c] = opcodes[mnemonic](regs, a, b)

	regs[ipreg] += 1

sys.stderr.write('\n')

print(i)
print(regs)

ans = regs[0]

advent.submit_answer(1, ans)


divsum = 0
for i in range(1, 10551319 + 1):
	if 10551319 % i == 0:
		divsum += i

# 103 too low
# 111330332639761 too high
# 55665171595540 too high
# 600041 wrong
advent.submit_answer(2, divsum)
