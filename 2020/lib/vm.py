import sys
from math import inf

def log(s, *a):
	sys.stderr.write(s.format(*a))
	sys.stderr.flush()

class VMRuntimeError(Exception):
	pass

class VM:
	def __init__(self, source, inp=None, out=None):
		self.inp = inp # deque or None
		self.out = out # deque or None
		self.reset()
		self.parse_program(source)

	def parse_program(self, source):
		self.prog = []

		for line in source.splitlines():
			# Assume args will be separated by spaces only
			op, *args = line.split()

			# Treat everything as immediate for now
			nargs = len(args)
			types = (ARGTYPE_IMMEDIATE,) * nargs
			args  = tuple(map(int, args))

			# for i in range(nargs):
			# 	if types[i] == ARGTYPE_IMMEDIATE:
			# 		args[i] = int(args[i])

			self.prog.append((op, args, types))

		self.prog_len = len(self.prog)

	def reset(self):
		self.pc  = 0
		self.acc = 0
		self.running = True

	def run(self, steps=inf, debug=False):
		while steps:
			op, args, types = self.prog[self.pc]

			if debug:
				fmt = '{:4d}: {:4s}'

				for t, a in zip(types, args):
					fmt += '{} '

				log(fmt + '\n', self.pc, op, *args)

			if op == 'acc':
				self.acc += args[0]
			elif op == 'jmp':
				self.pc += args[0] - 1

			self.pc += 1
			if self.pc == self.prog_len:
				self.running = False
				break

			if not (0 <= self.pc < self.prog_len):
				raise VMRuntimeError('bad program counter')

			steps -= 1

ARGTYPE_IMMEDIATE = 0
ARGTYPES = {
	'nop': None,
	'acc': (ARGTYPE_IMMEDIATE,),
	'jmp': (ARGTYPE_IMMEDIATE,)
}
