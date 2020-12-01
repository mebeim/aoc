#!/usr/bin/env python3

from utils.all import *
from itertools import permutations

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

	def pp(self, debug=False):
		s = '{:>6d}:  '.format(self.pc)

		opcode = self.vm.code[self.pc]
		s += '{:03d} {:02d} '.format(opcode // 100, opcode % 100)
		s += '    {:<4s}'.format(self.mnemonic)

		if debug:
			l = len(self.args) - 1
			o = self.mnemonic not in ('jnz', 'jz', 'out')

			for i, (a, m) in enumerate(zip(self.args, self.argmodes)):
				if m == ARGMODE_DEREF:
					s += '{:>7s}'.format('[{:d}]'.format(a))

					if not o or i != l:
						s += '→{:<11d}'.format(self.decode_arg(i))
				else:
					s += '{:<11d}'.format(a).rjust(19)
		else:
			for a, m in zip(self.args, self.argmodes):
				if m == ARGMODE_DEREF:
					s += '{:>10s}] '.format('[{:d}'.format(a))
				else:
					s += '{:>10s}  '.format('{:d}'.format(a))

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
		self.input  = None
		self.output = None
		self.in_ptr = 0
		self.stop_at_out = False

	def dis(self):
		self.code = self.orig_code[:]
		self.mem = self.code

		while self.pc < len(self.code):
			op = Op.fromcode(self, self.pc)
			op.pp()

			self.pc += op.length

	def run(self, inp, debug=False):
		self.input  = inp
		self.in_ptr = 0
		self.output = []
		self.code = self.orig_code[:]
		self.mem = self.code
		self.running = True
		self.pc = 0

		while self.running:
			op = Op.fromcode(self, self.pc)

			if debug:
				op.pp(True)

			try:
				op.exec()
			except VMRuntimeError as e:
				sys.stderr.write('FATAL runtime error: ' + str(e) + '\n')
				return None

		return self.output

	def reset(self):
		self.in_ptr = 0
		self.output = []
		self.input = []
		self.code = self.orig_code[:]
		self.mem = self.code
		self.running = True

	def run_one_out(self, inp, debug=False):
		self.stop_at_out = True
		self.input  += inp

		while self.running:
			op = Op.fromcode(self, self.pc)

			if debug:
				op.pp(True)

			try:
				op.exec()

				if type(op) == OpOut:
					return self.output[-1]

			except VMRuntimeError as e:
				sys.stderr.write('FATAL runtime error: ' + str(e) + '\n')
				return None

		return None

	def read(self):
		value = self.input[self.in_ptr]
		self.in_ptr += 1
		return value

	def write(self, value):
		self.output.append(value)

	def halt(self):
		self.running = False

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

##################################################

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

ints = get_ints(fin, True)

vms = []
vms.append(IntcodeVM(ints))
vms.append(IntcodeVM(ints))
vms.append(IntcodeVM(ints))
vms.append(IntcodeVM(ints))
vms.append(IntcodeVM(ints))

maxo = float('-inf')
maxin = ()
errs = 0
old = []

D = (
	# True,
	# True,
	# True,
	# True,
	# True,
	False,
	False,
	False,
	False,
	False
)

for a, b, c, d, e in permutations(range(5), 5):
	# print(a, b, c, d, e)

	# if (a==4 and b==3 and c==2 and d==1 and e==0):
	# 	D = (
	# 		True,
	# 		True,
	# 		True,
	# 		True,
	# 		True,)

	o = vms[0].run([a, 0], debug=D[0])
	if D[0]: print('-'*20, o)

	o = vms[1].run([b, *o], debug=D[1])
	if D[1]: print('-'*20, o)

	o = vms[2].run([c, *o], debug=D[2])
	if D[2]: print('-'*20, o)

	o = vms[3].run([d, *o], debug=D[3])
	if D[3]: print('-'*20, o)

	o = vms[4].run([e, *o], debug=D[4])
	if D[4]: print('-'*20, o)

	# print('->', o, maxo)

	assert len(o) == 1

	if o[0] > maxo:
		old.append(maxo)
		maxo = o[0]
		maxin = (a,b,c,d,e)

	# if (a==0 and b==0 and c==0 and d==0 and e==0):
	# if (a==4 and b==3 and c==2 and d==1 and e==0):
	# if (a==1 and b==2 and c==3 and d==4 and e==5):
		# print(o)
		# break

# print('---------- err  ', errs)
print('---------- max  ', maxo)
# print('---------- maxin', maxin)
# print(old)

# 15494732 wrong
advent.submit_answer(1, maxo)

maxo = float('-inf')
maxin = ()
errs = 0
old = []

D = (
	# True,
	# True,
	# True,
	# True,
	# True,
	False,
	False,
	False,
	False,
	False
)

for a, b, c, d, e in permutations(range(5, 10), 5):
	# print(a, b, c, d, e)

	# if (a==4 and b==3 and c==2 and d==1 and e==0):
	# 	D = (
	# 		True,
	# 		True,
	# 		True,
	# 		True,
	# 		True,)

	vms = []
	vms.append(IntcodeVM(ints))
	vms.append(IntcodeVM(ints))
	vms.append(IntcodeVM(ints))
	vms.append(IntcodeVM(ints))
	vms.append(IntcodeVM(ints))

	for vm in vms:
		vm.reset()

	o = vms[0].run_one_out([a, 0], debug=D[0])
	if D[0]: print('-'*20, o)

	o = vms[1].run_one_out([b, o], debug=D[1])
	if D[1]: print('-'*20, o)

	o = vms[2].run_one_out([c, o], debug=D[2])
	if D[2]: print('-'*20, o)

	o = vms[3].run_one_out([d, o], debug=D[3])
	if D[3]: print('-'*20, o)

	o = vms[4].run_one_out([e, o], debug=D[4])
	if D[4]: print('-'*20, o)

	while vms[4].running:
		o = vms[0].run_one_out([o], debug=D[0])
		if D[0]: print('-'*20, o)

		o = vms[1].run_one_out([o], debug=D[1])
		if D[1]: print('-'*20, o)

		o = vms[2].run_one_out([o], debug=D[2])
		if D[2]: print('-'*20, o)

		o = vms[3].run_one_out([o], debug=D[3])
		if D[3]: print('-'*20, o)

		o = vms[4].run_one_out([o], debug=D[4])
		if D[4]: print('-'*20, o)

		if o is not None:
			oo = o

	# print('->', o, maxo)

	if oo > maxo:
		old.append(maxo)
		maxo = oo
		maxin = (a,b,c,d,e)

# print('---------- err  ', errs)
print('---------- max  ', maxo)
# print('---------- maxin', maxin)
# print(old)

# 61696857 wrong
advent.submit_answer(2, maxo)
