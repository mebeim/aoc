#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 16)
DEBUG = 'debug' not in map(str.lower, sys.argv)
if DEBUG:
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
9C0141080250320F1802104A08
''')

eprint(*fin, sep='', end='----- end of input -----\n\n'); fin.seek(0, 0)
timer_start()

prog = fin.read().strip()
prog = bytes.fromhex(prog)


bits = ''
for p in prog:
	bits += '{:08b}'.format(p)
# bits = list(map(int, bits))


ans = 0
i = 0
n = len(bits)

def parse(bits, n, npackets=INFINITY, depth=0):
	log = rlog(depth)

	global ans
	res = []
	i = 0

	while i < n and npackets > 0:
		log('i {} n {} np {} {}...\n', i, n, npackets, bits[:40])
		if i + 6 >= n:
			return i, res

		v = int(bits[i:i+3],2)
		i += 3
		t = int(bits[i:i+3], 2)
		i += 3

		ans += v

		if t == 4:
			num = 0
			while i < n:
				a = int(bits[i:i+5],2)
				num <<= 4
				num += a & 0xf
				if not (a & (1 << 4)):
					i += 5
					break
				i += 5

			log('v {} t {} num {}\n', v, t, num)

			res.append((v, t, num))
		else:
			tid = int(bits[i])
			i += 1

			if tid == 0:
				l = 15
			else:
				l = 11

			nsub = int(bits[i:i+l], 2)
			i += l

			log('v {} t {} tid {} {} {}\n', v, t, tid, 'sublen' if tid == 0 else 'nsub', nsub)

			if tid == 0:
				end, data = parse(bits[i:], nsub, INFINITY, depth+1)
				res.append((v, t, tid, nsub, data))
			else:
				end, data = parse(bits[i:], len(bits[i:]), nsub, depth+1)
				res.append((v, t, tid, nsub, data))

			i += end

		npackets -= 1
		log('after i {} n {} np {}\n', i, n, npackets)

	log('-> res: {} {}...\n', i, repr(res)[:100])
	return i, res

_, data = parse(bits, len(bits))

advent.print_answer(1, ans)
# wait('Submit? ')
# advent.submit_answer(1, ans)

def evaluate(pkt, depth=0):
	log = rlog(depth)
	log('pkt: {}\n', repr(pkt)[:200])

	v, t, *rest = pkt

	if t == 4:
		num = rest[0]
		return num
	else:
		tid, nsub, sub = rest
		log('v {} t {} tid {} {} {} subpkts {}\n', v, t, tid, 'sublen' if tid == 0 else 'nsub', nsub, len(sub))

		if t == 0:
			log('sum\n')
			res = 0
			for p in sub:
				res += evaluate(p, depth+1)
		elif t == 1:
			log('prod\n')
			res = 1
			for p in sub:
				res *= evaluate(p, depth+1)
		elif t == 2:
			log('min\n')
			res = INFINITY
			for p in sub:
				x = evaluate(p, depth+1)
				if x < res:
					res = x
		elif t == 3:
			log('max\n')
			res = -INFINITY
			for p in sub:
				x = evaluate(p, depth+1)
				if x > res:
					res = x
		elif t == 5:
			log('gt\n')
			a = evaluate(sub[0], depth+1)
			b = evaluate(sub[1], depth+1)
			res = 1 if a > b else 0
		elif t == 6:
			log('lt\n')
			a = evaluate(sub[0], depth+1)
			b = evaluate(sub[1], depth+1)
			res = 1 if a < b else 0
		elif t == 7:
			log('eq\n')
			a = evaluate(sub[0], depth+1)
			b = evaluate(sub[1], depth+1)
			res = 1 if a == b else 0
		else:
			assert False

	log('res: {}\n', res)
	return res

assert len(data) == 1

eprint()
eprint()

ans = evaluate(data[0])

# 40346805699675698927593428 nope
advent.print_answer(2, ans)
# wait('Submit? ')
# advent.submit_answer(2, ans)
