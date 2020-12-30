#!/usr/bin/env python3

from utils import advent
from math import inf

class VM:
	__slots__ = ('prog', 'prog_len', 'pc', 'acc', 'running')

	def __init__(self, source):
		self.reset()
		self.parse_program(source)

	def parse_program(self, source):
		self.prog = []

		for line in source.splitlines():
			op, *args = line.split()
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

			if op == 'acc':
				self.acc += args[0]
			elif op == 'jmp':
				self.pc += args[0] - 1

			self.pc += 1
			if self.pc == self.prog_len:
				self.running = False
				break

			steps -= 1


advent.setup(2020, 8)
fin = advent.get_input()

source = fin.read()
vm     = VM(source)
seen   = set()

while vm.pc not in seen:
	seen.add(vm.pc)
	vm.run(1)

advent.print_answer(1, vm.acc)


for i in range(1, vm.prog_len):
	original = vm.prog[i]

	if original[0] == 'acc':
		continue
	elif original[0] == 'jmp':
		vm.prog[i] = ('nop',) + original[1:]
	elif original[0] == 'nop':
		vm.prog[i] = ('jmp',) + original[1:]

	vm.reset()
	seen = set()

	while vm.running and vm.pc not in seen:
		seen.add(vm.pc)
		vm.run(1)

	if not vm.running:
		break

	vm.prog[i] = original

advent.print_answer(2, vm.acc)
