#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 14)
fin = advent.get_input()

# fin = io.StringIO('''\
# mask = 000000000000000000000000000000X1001X
# mem[42] = 100
# mask = 00000000000000000000000000000000X0XX
# mem[26] = 1
# ''')

eprint(*fin, sep=''); fin.seek(0, 0)
timer_start()
lines = get_lines(fin)

mem = [0] * 1000000

for l in lines:
	if l.startswith('mask'):
		l = l[len('mask = '):].strip()
		override = {}
		for i, c in enumerate(l[::-1]):
			if c == '1':
				override[i] = 1 << i
			elif c == '0':
				override[i] = 0
			# eprint(override)
	elif l.startswith('mem'):
		addr, v = re.findall(r'mem\[(\d+)\] = (\d+)', l)[0]
		addr, v = int(addr), int(v)
		# eprint(addr, v)
		for o in override:
			res = (v & (0xfffffffff - (1 << o))) + override[o]

			# eprint(bin(v).rjust(40))
			# eprint(bin((0xfffffffff - (1 << o))).rjust(40))
			# eprint(bin(res).rjust(40))
			# eprint()

			mem[addr] = res
			v = mem[addr]
	else:
		assert False

# for i, x in enumerate(mem[:3]):
# 	print(i, ':', bin(x).rjust(40))

ans = sum(mem)
advent.print_answer(1, ans)


mem = {}
from itertools import product

# Oh almighty gods of programming forgive me for my immortal sins
def write_mem(addr, value, mask):
	orig = addr
	power = 0

	for k, v in mask.items():
		if v == 'X':
			power += 1
		else:
			addr = addr | v

	addr = list(bin(addr)[2:].rjust(36, '0'))
	for i in range(36):
		if i in mask and mask[i] == 'X':
			addr[35-i] = 'X'

	n = 2 ** power
	str_addr = ''.join(addr)

	# eprint(bin(orig)[2:].rjust(36, '0'))
	# eprint(str_addr)
	# eprint('---- n:', n)

	for comb in range(n):
		a = addr[:]
		i = -1

		# eprint('c:', bin(comb)[2:].rjust(power, '0'))

		for b in bin(comb)[2:].rjust(power, '0'):
			i = str_addr.find('X', i + 1)

			if b == '1':
				a[i] = '1'
			else:
				a[i] = '0'

		a = ''.join(a)
		a = int(a, 2)
		mem[a] = value

		# eprint('m[{:036b}] = {:036b}'.format(a, value))

for l in lines:
	if l.startswith('mask'):
		l = l[len('mask = '):].strip()
		override = {}
		for i, c in enumerate(l[::-1]):
			if c == '1':
				override[i] = 1 << i
			elif c == 'X':
				override[i] = 'X'
	elif l.startswith('mem'):
		addr, v = re.findall(r'mem\[(\d+)\] = (\d+)', l)[0]
		addr, v = int(addr), int(v)
		write_mem(addr, v, override)
	else:
		assert False

# for i, x in mem.items():
# 	print(i, ':', bin(x).rjust(40))

ans2 = sum(mem.values())
advent.print_answer(2, ans2)
