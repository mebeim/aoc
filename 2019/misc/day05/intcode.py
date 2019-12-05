#!/usr/bin/env python3

import sys

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
			raise VMRuntimeError('invalid program counter (pc = {:d}'.format(self.pc))

		div = 100
		opcode = self.vm.code[self.pc]

		for _ in range(n_args):
			i = self.pc + self.length

			if i >= len(self.vm.code):
				raise VMRuntimeError('incomplete instruction (pc = {:d}'.format(self.pc))

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

	def pp(self):
		s = '{:>6d}:  '.format(self.pc)

		opcode = self.vm.code[self.pc]
		s += '{:03d} {:02d} '.format(opcode // 100, opcode % 100)
		s += '    {:<4s}'.format(self.mnemonic)

		for a, m in zip(self.args, self.argmodes):
			if m == ARGMODE_DEREF:
				s += '{:>8s}] '.format('[{:d}'.format(a))
			else:
				s += '{:>8s}  '.format('{:d}'.format(a))

		sys.stderr.write(s.rstrip() + '\n')

	def read_mem(self, addr):
		if addr < 0 or addr >= len(self.vm.mem):
			raise VMRuntimeError('out of bounds memory read at {:d} (pc = {:d})'.format(addr, self.pc))

		return self.vm.mem[addr]

	def write_mem(self, addr, value):
		if addr < 0 or addr >= len(self.vm.mem):
			raise VMRuntimeError('out of bounds memory write at {:d} (pc = {:d})'.format(addr, self.pc))

		self.vm.mem[addr] = value

	def decode_arg(self, i):
		a, m = self.args[i], self.argmodes[i]

		if m == ARGMODE_DEREF:
			return self.read_mem(a)
		elif m == ARGMODE_IMMEDIATE:
			return a
		else:
			raise VMRuntimeError('invalid argument {:d} mode {:d} (pc = {:d})'.format(i, m, self.pc))

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
		self.write_mem(self.args[2], self.decode_arg(0) + self.decode_arg(1))
		self.vm.pc += self.length

class OpMul(Op):
	def __init__(self, vm, pc):
		super(OpMul, self).__init__(vm, pc, 'mul', 3)

	def exec(self):
		self.write_mem(self.args[2], self.decode_arg(0) * self.decode_arg(1))
		self.vm.pc += self.length

class OpIn(Op):
	def __init__(self, vm, pc):
		super(OpIn, self).__init__(vm, pc, 'in', 1)

	def exec(self):
		self.write_mem(self.args[0], self.vm.read())
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
		a, b = self.decode_arg(0), self.decode_arg(1)
		self.write_mem(self.args[2], 1 if a < b else 0)
		self.vm.pc += self.length

class OpEq(Op):
	def __init__(self, vm, pc):
		super(OpEq, self).__init__(vm, pc, 'eq', 3)

	def exec(self):
		a, b = self.decode_arg(0), self.decode_arg(1)
		self.write_mem(self.args[2], 1 if a == b else 0)
		self.vm.pc += self.length

class OpHlt(Op):
	def __init__(self, vm, pc):
		super(OpHlt, self).__init__(vm, pc, 'hlt', 0)
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
			op = Op.fromcode(self, self.pc)
			op.pp()

			self.pc += op.length

	def run(self, debug=False):
		self.code = self.orig_code[:]
		self.mem = self.code
		self.running = True

		while vm.running:
			op = Op.fromcode(self, self.pc)

			if debug:
				op.pp()

			try:
				op.exec()
			except VMRuntimeError as e:
				sys.stderr.write('FATAL runtime error: ' + str(e) + '\n')
				return 1

		return 0

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

if __name__ == '__main__':
	if len(sys.argv) != 3:
		usage()

	with open(sys.argv[2]) as fin:
		program = list(map(int, fin.read().split(',')))

	vm = IntcodeVM(program)

	if sys.argv[1] == 'run':
		res = vm.run()
		sys.exit(res)
	elif sys.argv[1] == 'debug':
		res = vm.run(True)
		sys.exit(res)
	elif sys.argv[1] == 'dis':
		vm.dis()
	else:
		usage()
