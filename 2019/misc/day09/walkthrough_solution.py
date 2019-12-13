#!/usr/bin/env python3

import sys

TYPE_SRC, TYPE_DST = range(2)
MODE_POSITION, MODE_IMMEDIATE, MODE_RELATIVE = range(3)
OPADD, OPMUL, OPIN, OPOUT, OPJNZ, OPJZ, OPLT, OPEQ, OPREL = range(1, 10)
OPHALT = 99

OPCODE_NPARAMS = {
	OPADD : 3,
	OPMUL : 3,
	OPIN  : 1,
	OPOUT : 1,
	OPJNZ : 2,
	OPJZ  : 2,
	OPLT  : 3,
	OPEQ  : 3,
	OPREL : 1,
	OPHALT: 0
}

OPCODE_PARAMTYPES = {
	OPADD : (TYPE_SRC, TYPE_SRC, TYPE_DST),
	OPMUL : (TYPE_SRC, TYPE_SRC, TYPE_DST),
	OPIN  : (TYPE_DST,),
	OPOUT : (TYPE_SRC,),
	OPJNZ : (TYPE_SRC, TYPE_SRC),
	OPJZ  : (TYPE_SRC, TYPE_SRC),
	OPLT  : (TYPE_SRC, TYPE_SRC, TYPE_DST),
	OPEQ  : (TYPE_SRC, TYPE_SRC, TYPE_DST),
	OPREL : (TYPE_SRC,),
	OPHALT: ()
}

def run(prog, input_function, output_function):
	pc = 0
	relative_base = 0

	# Extend memory filling with zeros.
	prog = prog + [0] * 10000

	while prog[pc] != OPHALT:
		op = prog[pc]

		# Calculate parameter modes.
		modes = ((op // 100) % 10, (op // 1000) % 10, (op // 10000) % 10)
		op = op % 10

		# Get parameters and parameter types.
		nparams = OPCODE_NPARAMS[op]
		types   = OPCODE_PARAMTYPES[op]
		params  = prog[pc + 1:pc + 1 + nparams]

		# Translate parameters into the needed values based on the mode.
		for i in range(len(params)):
			if modes[i] == MODE_POSITION:
				if types[i] == TYPE_SRC:
					params[i] = prog[params[i]]
			elif modes[i] == MODE_RELATIVE:
				if types[i] == TYPE_SRC:
					params[i] = prog[relative_base + params[i]]
				elif types[i] == TYPE_DST:
					params[i] += relative_base

		if op == OPADD:
			a, b, c = params
			prog[c] = a + b
			pc += 4
		elif op == OPMUL:
			a, b, c = params
			prog[c] = a * b
			pc += 4
		elif op == OPIN:
			a = params[0]
			prog[a] = input_function()
			pc += 2
		elif op == OPOUT:
			a = params[0]
			output_function(a)
			pc += 2
		elif op == OPJNZ:
			a, b = params
			pc = b if a != 0 else pc + 3
		elif op == OPJZ:
			a, b = params
			pc = b if a == 0 else pc + 3
		elif op == OPLT:
			a, b, c = params
			prog[c] = 1 if a < b else 0
			pc += 4
		elif op == OPEQ:
			a, b, c = params
			prog[c] = 1 if a == b else 0
			pc += 4
		elif op == OPREL:
			a = params[0]
			relative_base += a
			pc += 2


if len(sys.argv) != 2:
	sys.stderr.write('Usage: {} day09_input.txt')
	sys.exit(1)

fin = open(sys.argv[1])
program = list(map(int, fin.read().split(',')))
output_value = None

def out_func(v):
	global output_value
	output_value = v

in_func = lambda: 1
run(program[:], in_func, out_func)
print('Part 1:', output_value)


in_func = lambda: 2
run(program[:], in_func, out_func)
print('Part 2:', output_value)
