#!/usr/bin/env python3

from utils.all import *
from lib.vm import VM

advent.setup(2020, 8)
fin = advent.get_input()

source = fin.read()
vm = VM(source)
seen = set()

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
