#!/usr/bin/env python3

from utils.all import *


def run(code, a, b, c):
	pc = 0
	out = []

	def combo(v):
		if 0 <= v <= 3:
			return v
		if v == 4:
			return a
		if v == 5:
			return b
		if v == 6:
			return c
		assert False, v

	while pc < len(code):
		op, imm = code[pc:pc+2]

		if op == 0:
			a = a // (2**combo(imm))
		elif op == 1:
			b = b ^ imm
		elif op == 2:
			b = combo(imm) % 8
		elif op == 3:
			if a != 0:
				pc = imm
				continue
		elif op == 4:
			b = b ^ c
		elif op == 5:
			out.append(combo(imm) % 8)
		elif op == 6:
			b = a // (2**combo(imm))
		elif op == 7:
			c = a // (2**combo(imm))

		pc += 2

	return out


def solve():
	# do
	# {
	#     printf("%llu,", ((unsigned __int8)((a / (1 << (a & 7 ^ 6))) ^ a & 7 ^ 6) ^ 4) & 7);
	#     olda = a;
	#     a >>= 3;
	# }
	# while ( olda > 7 );

	s = z3.Optimize()
	orig = a = z3.BitVec('a', 64)

	for x in [2,4,1,6,7,5,4,6,1,4,5,5,0,3,3,0]:
		b = a & 7
		b ^= 6
		c = a >> b
		b ^= c
		b ^= 4
		s.add((b & 7) == x)
		a = a >> 3

	s.add(a == 0)
	s.minimize(orig)
	assert s.check() == z3.sat
	return s.model().eval(orig)


DEBUG = 'debug' in map(str.lower, sys.argv)

if not DEBUG:
	a = 66171486
	b = c = 0
	code = [2,4,1,6,7,5,4,6,1,4,5,5,0,3,3,0]
else:
	a = 729
	b = c = 0
	code = [0,1,5,4,3,0]

out = run(code, a, b, c)
ans1 = ','.join(map(str, out))
advent.print_answer(1, ans1)


# 90938893795567 wrong
# 90938893815382 wrong
# 90938893795561
ans2 = solve()
advent.print_answer(2, ans2)
