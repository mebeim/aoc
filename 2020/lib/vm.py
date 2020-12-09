import sys
from math import inf

def log(s, *a):
	sys.stderr.write(s.format(*a))
	sys.stderr.flush()

class VMRuntimeError(Exception):
	pass

class VM:
	__slots__ = ('prog', 'prog_len', 'pc', 'acc', 'running', 'inp', 'out')

	def __init__(self, source, inp=None, out=None):
		self.inp = inp # deque or None
		self.out = out # deque or None
		self.reset()
		self.parse_program(source)

	def parse_program(self, source):
		self.prog = []

		for line in source.splitlines():
			# Assume ops and args will be separated by spaces only
			op, *args = line.split()

			# Treat every arg as an immediate integer for now
			args  = tuple(map(int, args))
			self.prog.append((op, args))

		self.prog_len = len(self.prog)

	def reset(self):
		self.pc  = 0
		self.acc = 0
		self.running = True

	def run(self, steps=inf, debug=False):
		while steps:
			op, args = self.prog[self.pc]

			if debug:
				fmt = '{:4d}: {:4s}' + '{} ' * len(args) + '\n'
				log(fmt, self.pc, op, *args)

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
