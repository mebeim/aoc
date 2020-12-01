#!/usr/bin/env python3

from utils import advent
import re
import z3

def solve(ops):
	solver = z3.Solver()
	variables = []

	for i, possible in enumerate(ops):
		x = z3.Int(i)
		solver.add(z3.Or(*(x == v for v in possible)))
		solver.add(z3.And(*(x != y for y in variables)))
		variables.append(x)

	solver.check()
	m = solver.model()

	return tuple(map(z3.IntNumRef.as_long, map(m.eval, variables)))

opcodes = [
	lambda r,a,b: r[a] + r[b],             #  0 addr
	lambda r,a,b: r[a] + b,                #  1 addi
	lambda r,a,b: r[a] * r[b],             #  2 mulr
	lambda r,a,b: r[a] * b,                #  3 muli
	lambda r,a,b: r[a] & r[b],             #  4 banr
	lambda r,a,b: r[a] & b,                #  5 bani
	lambda r,a,b: r[a] | r[b],             #  6 borr
	lambda r,a,b: r[a] | b,                #  7 bori
	lambda r,a,b: r[a],                    #  8 setr
	lambda r,a,b: a,                       #  9 seti
	lambda r,a,b: 1 if a > r[b] else 0,    # 10 gtir
	lambda r,a,b: 1 if r[a] > b else 0,    # 11 gtri
	lambda r,a,b: 1 if r[a] > r[b] else 0, # 12 gtrr
	lambda r,a,b: 1 if a == r[b] else 0,   # 13 eqir
	lambda r,a,b: 1 if r[a] == b else 0,   # 14 eqri
	lambda r,a,b: 1 if r[a] == r[b] else 0 # 15 eqrr
]

opmap = list(set(range(16)) for i in range(16))
rexp  = re.compile(r'-?\d+')


advent.setup(2018, 16)
fin = advent.get_input()

data    = fin.read().strip().split('\n\n\n\n')
samples = [l.split('\n') for l in data[0].split('\n\n')]
program = [tuple(map(int, l.split())) for l in data[1].split('\n')]

ans = 0

for sample in samples:
	before = tuple(map(int, rexp.findall(sample[0])))
	instr  = tuple(map(int, rexp.findall(sample[1])))
	after  = tuple(map(int, rexp.findall(sample[2])))

	count = 0
	for op_id, op in enumerate(opcodes):
		if op(before, instr[1], instr[2]) == after[instr[3]]:
			count += 1
		elif op_id in opmap[instr[0]]:
			opmap[instr[0]].remove(op_id)

	if count >= 3:
		ans += 1

advent.print_answer(1, ans)


opmap = solve(opmap)

regs = [0] * 4
for instr in program:
	regs[instr[3]] = opcodes[opmap[instr[0]]](regs, instr[1], instr[2])

ans2 = regs[0]
advent.print_answer(2, ans2)
