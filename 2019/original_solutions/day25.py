#!/usr/bin/env python3

from utils.all import *

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

from lib.intcode import IntcodeVM
prog = get_ints(fin, True)
vm = IntcodeVM(prog)

Q = deque()
N, S, E, W = 'north', 'south', 'east', 'west'

def vm_read_for(self):
	def vm_read():
		if not Q:
			line = input()
			if line == 'n':
				line = N
			elif line == 's':
				line = S
			elif line == 'e':
				line = E
			elif line == 'w':
				line = W
			Q.extend(map(ord, line + '\n'))
		return Q.popleft()

	return vm_read

def vm_write(v):
	if v <= 127:
		sys.stdout.write(chr(v))
	else:
		print('----------', v)

vm.read = vm_read_for(vm)
vm.write = vm_write

# Solve manually! :P
vm.run()
