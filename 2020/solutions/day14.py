#!/usr/bin/env python3

from utils import advent
import re
from itertools import product

def all_addrs(addr, mask):
	args = []

	for addr_bit, mask_bit in zip(addr, mask):
		if mask_bit == '0':
			args.append(addr_bit)
		elif mask_bit == '1':
			args.append('1')
		else:
			args.append('01')

	for a in product(*args):
		yield int(''.join(a), 2)

# Alternative manual implementation which takes addr after applying mask to it.
#
# def all_addrs(addr):
# 	if 'X' in addr:
# 		yield from all_addrs(addr.replace('X', '0', 1))
# 		yield from all_addrs(addr.replace('X', '1', 1))
# 	else:
# 		yield int(addr, 2)


advent.setup(2020, 14)
fin = advent.get_input()

lines = fin.readlines()
rexp = re.compile(r'mem\[(\d+)\] = (\d+)')
table = str.maketrans('1X', '01')

mem = {}
for line in lines:
	if line.startswith('mask'):
		mask      = line[7:].rstrip()
		real_mask = int(mask.translate(table), 2)
		addend    = int(mask.replace('X', '0'), 2)
	else:
		addr, value = map(int, rexp.findall(line)[0])
		mem[addr] = (value & real_mask) | addend

total = sum(mem.values())
advent.print_answer(1, total)


mem = {}
for line in lines:
	if line.startswith('mask'):
		mask = line[7:].rstrip()
	else:
		addr, value = map(int, rexp.findall(line)[0])
		addr = '{:036b}'.format(addr)

		for a in all_addrs(addr, mask):
			mem[a] = value

total = sum(mem.values())
advent.print_answer(2, total)
