#!/usr/bin/env python3

import sys
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

# Alternative manual implementation.
#
# def all_addrs(addr, mask=None):
# 	if mask is not None:
# 		addr = ''.join(a if m == '0' else m for a, m in zip(addr, mask))
#
# 	if 'X' in addr:
# 		yield from all_addrs(addr.replace('X', '0', 1))
# 		yield from all_addrs(addr.replace('X', '1', 1))
# 	else:
# 		yield int(addr, 2)


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

lines = fin.readlines()
rexp  = re.compile(r'mem\[(\d+)\] = (\d+)')
table = str.maketrans('1X', '01')
mem1  = {}
mem2  = {}

for line in lines:
	if line.startswith('mask'):
		mask       = line[7:].rstrip()
		mask_clear = int(mask.translate(table), 2)
		mask_set   = int(mask.replace('X', '0'), 2)
	else:
		addr, value = map(int, rexp.findall(line)[0])
		mem1[addr]  = (value & mask_clear) | mask_set

		addr = '{:036b}'.format(addr)
		for a in all_addrs(addr, mask):
			mem2[a] = value

total1 = sum(mem1.values())
total2 = sum(mem2.values())

print('Part 1:', total1)
print('Part 2:', total2)
