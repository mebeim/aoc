#!/usr/bin/env python3

import sys

class VMRuntimeError(Exception):
	pass

class Op:
	def __init__(self, vm, n_args=0):
		self.vm       = vm
		self.args     = []
		self.argmodes = []
		self.length   = 1
		self.mnemonic = '(bad)'

		if not (0 <= self.vm.pc < len(self.vm.code)):
			raise VMRuntimeError('invalid program counter')

		div = 100
		opcode = self.vm.code[self.vm.pc]

		for _ in range(n_args):
			i = self.vm.pc + self.length

			if i >= len(self.vm.code):
				raise VMRuntimeError('incomplete instruction')

			self.args.append(self.vm.code[i])
			self.argmodes.append(opcode // div % 10)
			self.length += 1
			div *= 10

	@staticmethod
	def fromcode(vm):
		op = vm.code[vm.pc] % 100
		if op in OPMAP:
			return OPMAP[op](vm)
		return OpInvalid(vm)

	def pp(self):
		s = '{:>6d}:  '.format(self.vm.pc)
		s += '{:<4s}'.format(self.mnemonic)

		for a, m in zip(self.args, self.argmodes):
			if m == ARGMODE_DEREF:
				s += '{:>8s}] '.format('[{:d}'.format(a).replace('0x-', '-0x'))
			else:
				s += '{:>8s}  '.format('{:d}'.format(a).replace('0x-', '-0x'))

		sys.stderr.write(s.rstrip() + '\n')

	def exec(self):
		raise NotImplementedError()

class OpInvalid(Op):
	def __init__(self, vm):
		super(OpInvalid, self).__init__(vm)

	def exec(self):
		raise VMRuntimeError('invalid opcode {:d} (pc = {:d})'.format(self.vm.code[self.vm.pc], self.vm.pc))

class OpAdd(Op):
	def __init__(self, vm):
		super(OpAdd, self).__init__(vm, 3)
		self.mnemonic = 'add'

	def exec(self):
		a = self.args[0] if self.argmodes[0] == ARGMODE_IMMEDIATE else self.vm.mem[self.args[0]]
		b = self.args[1] if self.argmodes[1] == ARGMODE_IMMEDIATE else self.vm.mem[self.args[1]]
		self.vm.mem[self.args[2]] = a + b
		self.vm.pc += self.length

class OpMul(Op):
	def __init__(self, vm):
		super(OpMul, self).__init__(vm, 3)
		self.mnemonic = 'mul'

	def exec(self):
		a = self.args[0] if self.argmodes[0] == ARGMODE_IMMEDIATE else self.vm.mem[self.args[0]]
		b = self.args[1] if self.argmodes[1] == ARGMODE_IMMEDIATE else self.vm.mem[self.args[1]]
		self.vm.mem[self.args[2]] = a * b
		self.vm.pc += self.length

class OpIn(Op):
	def __init__(self, vm):
		super(OpIn, self).__init__(vm, 1)
		self.mnemonic = 'in'

	def exec(self):
		self.vm.mem[self.args[0]] = self.vm.read()
		self.vm.pc += self.length

class OpOut(Op):
	def __init__(self, vm):
		super(OpOut, self).__init__(vm, 1)
		self.mnemonic = 'out'

	def exec(self):
		value = self.args[0] if self.argmodes[0] == ARGMODE_IMMEDIATE else self.vm.mem[self.args[0]]
		self.vm.write(value)
		self.vm.pc += self.length

class OpJnz(Op):
	def __init__(self, vm):
		super(OpJnz, self).__init__(vm, 2)
		self.mnemonic = 'jnz'

	def exec(self):
		value = self.args[0] if self.argmodes[0] == ARGMODE_IMMEDIATE else self.vm.mem[self.args[0]]
		addr = self.args[1] if self.argmodes[1] == ARGMODE_IMMEDIATE else self.vm.mem[self.args[1]]
		self.vm.pc = addr if value != 0 else self.vm.pc + self.length

class OpJz(Op):
	def __init__(self, vm):
		super(OpJz, self).__init__(vm, 2)
		self.mnemonic = 'jz'

	def exec(self):
		value = self.args[0] if self.argmodes[0] == ARGMODE_IMMEDIATE else self.vm.mem[self.args[0]]
		addr = self.args[1] if self.argmodes[1] == ARGMODE_IMMEDIATE else self.vm.mem[self.args[1]]
		self.vm.pc = addr if value == 0 else self.vm.pc + self.length

class OpLt(Op):
	def __init__(self, vm):
		super(OpLt, self).__init__(vm, 3)
		self.mnemonic = 'lt'

	def exec(self):
		a = self.args[0] if self.argmodes[0] == ARGMODE_IMMEDIATE else self.vm.mem[self.args[0]]
		b = self.args[1] if self.argmodes[1] == ARGMODE_IMMEDIATE else self.vm.mem[self.args[1]]
		self.vm.mem[self.args[2]] = 1 if a < b else 0
		self.vm.pc += self.length

class OpEq(Op):
	def __init__(self, vm):
		super(OpEq, self).__init__(vm, 3)
		self.mnemonic = 'eq'

	def exec(self):
		a = self.args[0] if self.argmodes[0] == ARGMODE_IMMEDIATE else self.vm.mem[self.args[0]]
		b = self.args[1] if self.argmodes[1] == ARGMODE_IMMEDIATE else self.vm.mem[self.args[1]]
		self.vm.mem[self.args[2]] = 1 if a == b else 0
		self.vm.pc += self.length

class OpHlt(Op):
	def __init__(self, vm):
		super(OpHlt, self).__init__(vm, 0)
		self.mnemonic = 'hlt'

	def exec(self):
		self.vm.halt()

class IntcodeVM:
	def __init__(self, code):
		self.pc        = 0
		self.orig_code = code
		self.code      = None
		self.mem       = None
		self.running   = True

	def dis(self):
		self.code = self.orig_code[:]
		self.mem = self.code

		while self.pc < len(self.code):
			op = Op.fromcode(self)
			op.pp()

			self.pc += op.length

	def run(self, debug=False):
		self.code = self.orig_code[:]
		self.mem = self.code
		self.running = True

		while vm.running:
			op = Op.fromcode(self)

			if debug:
				op.pp()

			op.exec()

	def read(self):
		value = int(input())
		return value

	def write(self, value):
		print(value)

	def halt(self):
		self.running = False

def usage():
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
	99: OpHlt
}

ARGMODE_DEREF, ARGMODE_IMMEDIATE = 0, 1

################################################################################

if len(sys.argv) != 3:
	usage()

with open(sys.argv[2]) as fin:
	program = list(map(int, fin.read().split(',')))

vm = IntcodeVM(program)

if sys.argv[1] == 'run':
	vm.run()
elif sys.argv[1] == 'debug':
	vm.run(True)
elif sys.argv[1] == 'dis':
	vm.dis()
else:
	usage()
