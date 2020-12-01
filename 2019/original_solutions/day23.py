#!/usr/bin/env python3

from utils.all import *

fin = advent.get_input()
timer_start()

##################################################

from lib.intcode import IntcodeVM
prog = get_ints(fin, True)

Q = []
for i in range(50):
	Q.append(deque([i]))

empty_reads = [0] * 50
idle = [False] * 50
outpkts = [[] for _ in range(50)]
natpkt = []

def vmr(addr):
	def vm_read():
		if Q[addr]:
			empty_reads[addr] = 0
			idle[addr] = False
			v = Q[addr].popleft()
			# eprint(addr, '<', v)
			return v
		else:
			empty_reads[addr] += 1
			if empty_reads[addr] > 2:
				idle[addr] = True
			return -1

	return vm_read

def vmw(addr):
	def vm_write(v):
		global natpkt

		empty_reads[addr] = 0
		idle[addr] = False
		outpkts[addr].append(v)

		if len(outpkts[addr]) == 3:
			# eprint(addr, '>', *outpkts[addr])

			recaddr = outpkts[addr][0]

			if recaddr == 255:
				natpkt = outpkts[addr][1:]
			else:
				Q[recaddr].append(outpkts[addr][1])
				Q[recaddr].append(outpkts[addr][2])

			outpkts[addr] = []

	return vm_write


vms = [IntcodeVM(prog) for _ in range(50)]

for i, vm in enumerate(vms):
	vm.read = vmr(i)
	vm.write = vmw(i)

for vm in vms:
	vm.reset()

while not all(idle):
	for vm in vms:
		vm.run(n_in=1, resume=True)
		if all(idle):
			break

last_nat_y = natpkt[1]
advent.submit_answer(1, last_nat_y)


last_nat_y = None
done = False

while not done:
	for vm in vms:
		vm.run(n_in=1, resume=True)

		if all(idle):
			assert len(natpkt) == 2
			# eprint('all idle, nat pkt:', *natpkt)

			idle[0] = False
			x, y = natpkt
			Q[0].append(x)
			Q[0].append(y)
			natpkt = []

			if y == last_nat_y:
				done = True
				advent.submit_answer(2, y)
				break

			last_nat_y = y
