#!/usr/bin/env python3
#
# Virtual Machine to execute, disassemble and debug Intcode programs.
# Disassembler output is always on standard error. Input is taken from standard
# input, each input number must followed by a newline. Output is printed to
# standard output.
#
# (C) 2019 Marco Bonelli -- https://github.com/mebeim/aoc
#

import sys

################## ONESHOT FAST IMPLEMENTATION ##################

OPCODE_NPARAMS = (None, 3, 3, 1, 1, 2, 2, 3, 3, 1)
OPCODE_PARAMTYPES = (
	None,
	(0, 0, 1),
	(0, 0, 1),
	(1,),
	(0,),
	(0, 0),
	(0, 0),
	(0, 0, 1),
	(0, 0, 1),
	(0,),
)

def intcode_oneshot(prog, inp=[]):
	inptr = 0
	pc = 0
	relative_base = 0
	prog = prog + [0] * 10000

	while prog[pc] != 99:
		op = prog[pc]

		modes = ((op // 100) % 10, (op // 1000) % 10, (op // 10000) % 10)
		op %= 10

		nparams = OPCODE_NPARAMS[op]
		types   = OPCODE_PARAMTYPES[op]
		params  = prog[pc + 1:pc + 1 + nparams]

		for i in range(len(params)):
			if modes[i] == 0:
				if types[i] == 0:
					params[i] = prog[params[i]]
			elif modes[i] == 2:
				if types[i] == 0:
					params[i] = prog[relative_base + params[i]]
				elif types[i] == 1:
					params[i] += relative_base

		if op == 1: # add
			prog[params[2]] = params[0] + params[1]
			pc += 4
		elif op == 2: # mul
			prog[params[2]] = params[0] * params[1]
			pc += 4
		elif op == 3: # in
			prog[params[0]] = inp[inptr]
			inptr += 1
			pc += 2
		elif op == 4: # out
			yield params[0]
			pc += 2
		elif op == 5: # jnz
			pc = params[1] if params[0] != 0 else pc + 3
		elif op == 6: # jz
			pc = params[1] if params[0] == 0 else pc + 3
		elif op == 7: # lt
			prog[params[2]] = 1 if params[0] < params[1] else 0
			pc += 4
		elif op == 8: # eq
			prog[params[2]] = 1 if params[0] == params[1] else 0
			pc += 4
		elif op == 9: # rel
			relative_base += params[0]
			pc += 2


################## COOL CLASS IMPLEMENTATION ##################

class VMRuntimeError(Exception):
	pass

class Op:
	def __init__(self, vm, pc, mnemonic='(bad)', n_args=0):
		self.vm       = vm
		self.pc       = pc
		self.args     = []
		self.argmodes = []
		self.length   = 1
		self.mnemonic = mnemonic

		if not (0 <= self.pc < len(self.vm.code)):
			raise VMRuntimeError('invalid program counter (pc = {:d})'.format(self.pc))

		div = 100
		opcode = self.vm.code[self.pc]

		for _ in range(n_args):
			i = self.pc + self.length

			if i >= len(self.vm.code):
				raise VMRuntimeError('incomplete instruction (pc = {:d})'.format(self.pc))

			self.args.append(self.vm.code[i])
			self.argmodes.append(opcode // div % 10)
			self.length += 1
			div *= 10

	@staticmethod
	def fromcode(vm, pc):
		op = vm.code[pc] % 100
		if op in OPMAP:
			return OPMAP[op](vm, pc)
		return OpInvalid(vm, pc)

	def pp(self, debug=False):
		s = '{:>6d}:  '.format(self.pc)

		opcode = self.vm.code[self.pc]
		s += '{:03d} {:02d} '.format(opcode // 100, opcode % 100)
		s += '    {:<4s}'.format(self.mnemonic)

		if debug:
			l = len(self.args) - 1
			o = self.mnemonic not in ('jnz', 'jz', 'out')

			for i, (a, m) in enumerate(zip(self.args, self.argmodes)):
				if m == ARGMODE_POSITIONAL:
					s += '{:>10s}'.format('[{:d}]'.format(a))

					if not o or i != l:
						s += '→{:<11d}'.format(self.decode_arg(i))
				elif m == ARGMODE_RELATIVE:
					s += '{:>10s}'.format('[{:d}{:s}{:d}]'.format(self.vm.relative_base, '+' if a >= 0 else '', a))

					if not o or i != l or type(self) == OpRel:
						s += '→{:<11d}'.format(self.decode_arg(i))
				else:
					s += '{:<11d}'.format(a).rjust(22)
		else:
			for a, m in zip(self.args, self.argmodes):
				if m == ARGMODE_POSITIONAL:
					s += '{:>13s}] '.format('[{:d}'.format(a))
				elif m == ARGMODE_RELATIVE:
					s += '{:>14s} '.format('[r{:s}{:d}]'.format('+' if a >= 0 else '', a))
				else:
					s += '{:>13s}  '.format('{:d}'.format(a))

		sys.stderr.write(s.rstrip() + '\n')

	def read_mem(self, addr):
		if addr < 0 or addr >= len(self.vm.mem):
			raise VMRuntimeError('out of bounds memory read at {:d} (pc = {:d})'.format(addr, self.pc))

		return self.vm.mem[addr]

	def write_mem(self, addr, value):
		if addr < 0 or addr >= len(self.vm.mem):
			raise VMRuntimeError('out of bounds memory write at {:d} (pc = {:d})'.format(addr, self.pc))

		self.vm.mem[addr] = value

	def decode_arg(self, i, is_destination=False):
		a, m = self.args[i], self.argmodes[i]

		if is_destination:
			if m == ARGMODE_POSITIONAL:
				return a
			elif m == ARGMODE_RELATIVE:
				return a + self.vm.relative_base
			else:
				raise VMRuntimeError('invalid argument #{:d} mode ({:d}) for instruction {:s} (pc = {:d})'.format(i + 1, m, self.mnemonic, self.pc))

		if m == ARGMODE_POSITIONAL:
			return self.read_mem(a)
		elif m == ARGMODE_IMMEDIATE:
			return a
		elif m == ARGMODE_RELATIVE:
			return self.read_mem(a + self.vm.relative_base)
		else:
			raise VMRuntimeError('invalid argument #{:d} mode ({:d}) for instruction {:s} (pc = {:d})'.format(i + 1, m, self.mnemonic, self.pc))

	def exec(self):
		raise NotImplementedError()

class OpInvalid(Op):
	def __init__(self, vm, pc):
		super(OpInvalid, self).__init__(vm, pc)

	def exec(self):
		raise VMRuntimeError('invalid opcode {:d} (pc = {:d})'.format(self.vm.code[self.pc], self.pc))

class OpAdd(Op):
	def __init__(self, vm, pc):
		super(OpAdd, self).__init__(vm, pc, 'add', 3)

	def exec(self):
		a, b, dst = self.decode_arg(0), self.decode_arg(1), self.decode_arg(2, True)
		self.write_mem(dst, a + b)
		self.vm.pc += self.length

class OpMul(Op):
	def __init__(self, vm, pc):
		super(OpMul, self).__init__(vm, pc, 'mul', 3)

	def exec(self):
		a, b, dst = self.decode_arg(0), self.decode_arg(1), self.decode_arg(2, True)
		self.write_mem(dst, a * b)
		self.vm.pc += self.length

class OpIn(Op):
	def __init__(self, vm, pc):
		super(OpIn, self).__init__(vm, pc, 'in', 1)

	def exec(self):
		addr = self.decode_arg(0, True)
		self.write_mem(addr, self.vm.read())
		self.vm.pc += self.length

class OpOut(Op):
	def __init__(self, vm, pc):
		super(OpOut, self).__init__(vm, pc, 'out', 1)

	def exec(self):
		self.vm.write(self.decode_arg(0))
		self.vm.pc += self.length

class OpJnz(Op):
	def __init__(self, vm, pc):
		super(OpJnz, self).__init__(vm, pc, 'jnz', 2)

	def exec(self):
		value, addr = self.decode_arg(0), self.decode_arg(1)
		self.vm.pc = addr if value != 0 else self.vm.pc + self.length

class OpJz(Op):
	def __init__(self, vm, pc):
		super(OpJz, self).__init__(vm, pc, 'jz', 2)

	def exec(self):
		value, addr = self.decode_arg(0), self.decode_arg(1)
		self.vm.pc = addr if value == 0 else self.vm.pc + self.length

class OpLt(Op):
	def __init__(self, vm, pc):
		super(OpLt, self).__init__(vm, pc, 'lt', 3)

	def exec(self):
		a, b, dst = self.decode_arg(0), self.decode_arg(1), self.decode_arg(2, True)
		self.write_mem(dst, 1 if a < b else 0)
		self.vm.pc += self.length

class OpEq(Op):
	def __init__(self, vm, pc):
		super(OpEq, self).__init__(vm, pc, 'eq', 3)

	def exec(self):
		a, b, dst = self.decode_arg(0), self.decode_arg(1), self.decode_arg(2, True)
		self.write_mem(dst, 1 if a == b else 0)
		self.vm.pc += self.length

class OpRel(Op):
	def __init__(self, vm, pc):
		super(OpRel, self).__init__(vm, pc, 'rel', 1)

	def exec(self):
		self.vm.relative_base += self.decode_arg(0)
		self.vm.pc += self.length

class OpHlt(Op):
	def __init__(self, vm, pc):
		super(OpHlt, self).__init__(vm, pc, 'hlt', 0)
		self.mnemonic = 'hlt'

	def exec(self):
		self.vm.halt()

class IntcodeVM:
	def __init__(self, code, as_exe=False):
		self.standalone_exe = as_exe
		self.orig_code      = code
		self.code           = None
		self.mem            = None
		self.input          = None
		self.output         = None
		self.first_run      = True
		self.need_reset     = True
		self.running        = True
		self.pc             = 0
		self.relative_base  = 0
		self.input_position = 0

	def dis(self):
		self.code = self.orig_code[:]
		self.mem  = self.code

		while self.pc < len(self.code):
			op = Op.fromcode(self, self.pc)
			op.pp()

			self.pc += op.length

	def reset(self):
		self.code          = self.orig_code[:] + [0] * 10000
		self.mem           = self.code
		self.pc            = 0
		self.relative_base = 0
		self.running       = True
		self.need_reset    = False

	def soft_reset(self):
		if self.code is None:
			self.code = self.orig_code[:] + [0] * 10000
			self.mem  = self.code

		self.pc            = 0
		self.relative_base = 0
		self.running       = True
		self.need_reset    = False

	def run(self, inp=None, n_out=-1, n_in=-1, resume=False, debug=False):
		if self.first_run or (not resume and self.need_reset):
			self.first_run = False
			self.reset()

		self.need_reset = True

		if self.standalone_exe:
			while self.running:
				op = Op.fromcode(self, self.pc)

				if debug:
					op.pp(True)

				try:
					op.exec()
				except VMRuntimeError as e:
					sys.stderr.write('FATAL runtime error: ' + str(e) + '\n')
					return 1

			return 0
		else:
			self.input = inp if inp is not None else []
			self.input_position = 0
			self.output = []

			while self.running:
				op = Op.fromcode(self, self.pc)

				if debug:
					op.pp(True)

				op.exec()

				if n_in > 0 and type(op) == OpIn:
					n_in -= 1
					if n_in == 0:
						break

				if n_out > 0 and type(op) == OpOut:
					n_out -= 1
					if n_out == 0:
						break

			return self.output

	def read(self):
		if self.standalone_exe:
			value = int(input())
		else:
			if self.input_position < len(self.input):
				value = self.input[self.input_position]
				self.input_position += 1
			else:
				raise VMRuntimeError('trying to read past the end of the input (index = {:d})'.format(self.input_position))

		return value

	def write(self, value):
		if self.standalone_exe:
			print(value)
		else:
			self.output.append(value)

	def halt(self):
		self.running = False

def _usage():
	sys.stderr.write('Usage: %s {run|debug|dis} intcode.txt\n' % sys.argv[0])
	sys.exit(1)

OPMAP = {
	1 : OpAdd,
	2 : OpMul,
	3 : OpIn,
	4 : OpOut,
	5 : OpJnz,
	6 : OpJz,
	7 : OpLt,
	8 : OpEq,
	9 : OpRel,
	99: OpHlt
}

ARGMODE_POSITIONAL, ARGMODE_IMMEDIATE, ARGMODE_RELATIVE = 0, 1, 2

if __name__ == '__main__':
	if len(sys.argv) != 3:
		_usage()

	with open(sys.argv[2]) as fin:
		program = list(map(int, fin.read().split(',')))

	vm = IntcodeVM(program, as_exe=True)

	if sys.argv[1] == 'run':
		res = vm.run()
		sys.exit(res)
	elif sys.argv[1] == 'debug':
		res = vm.run(debug=True)
		sys.exit(res)
	elif sys.argv[1] == 'dis':
		vm.dis()
	else:
		_usage()
