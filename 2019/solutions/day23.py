#!/usr/bin/env python3

from utils import advent
from lib.intcode import IntcodeVM
from collections import deque

def vm_read_for(self):
	def vm_read():
		if self.packet_queue:
			self.idle = False
			self.unserviced_reads = 0
			return self.packet_queue.popleft()

		self.unserviced_reads += 1
		if self.unserviced_reads > 1:
			self.idle = True

		return -1

	return vm_read

def vm_write_for(self):
	def vm_write(v):
		global nat_packet

		self.idle = False
		self.unserviced_reads = 0
		self.out_packet.append(v)

		if len(self.out_packet) == 3:
			destination, *packet = self.out_packet
			self.out_packet = []

			if destination == 255:
				nat_packet = packet
			else:
				network[destination].packet_queue.extend(packet)

	return vm_write


advent.setup(2019, 23)
fin = advent.get_input()

program = list(map(int, fin.read().split(',')))
network = [IntcodeVM(program) for _ in range(50)]
nat_packet = None

for i, vm in enumerate(network):
	vm.read             = vm_read_for(vm)
	vm.write            = vm_write_for(vm)
	vm.idle             = False
	vm.unserviced_reads = 0
	vm.packet_queue     = deque([i])
	vm.out_packet       = []

while nat_packet is None:
	for vm in network:
		vm.run(n_in=1, resume=True)

last_nat_y = nat_packet[1]
advent.print_answer(1, last_nat_y)


last_nat_y = None
done = False

while not done:
	for vm in network:
		vm.run(n_in=1, resume=True)

		if all(vm.idle for vm in network):
			if nat_packet[1] == last_nat_y:
				done = True
				break

			network[0].idle = False
			network[0].packet_queue.extend(nat_packet)

			last_nat_y = nat_packet[1]
			nat_packet = []

advent.print_answer(2, last_nat_y)
