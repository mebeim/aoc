#!/usr/bin/env python3

from utils import advent

advent.setup(2018, 16)
fin = advent.get_input()
# print(*fin)

##################################################

def simulate(r1, o, r2):
	op, a, b, c = o
	count = 0

	# addr
	if r2[c] == r1[a] + r1[b]: count += 1
	elif 'addr' in ops[op]: ops[op].remove('addr')

	# addi
	if r2[c] == r1[a] + b: count += 1
	elif 'addi' in ops[op]: ops[op].remove('addi')

	# mulr
	if r2[c] == r1[a] * r1[b]: count += 1
	elif 'mulr' in ops[op]: ops[op].remove('mulr')

	# muli
	if r2[c] == r1[a] * b: count += 1
	elif 'muli' in ops[op]: ops[op].remove('muli')

	# banr
	if r2[c] == r1[a] & r1[b]: count += 1
	elif 'banr' in ops[op]: ops[op].remove('banr')

	# bani
	if r2[c] == r1[a] & b: count += 1
	elif 'bani' in ops[op]: ops[op].remove('bani')

	# borr
	if r2[c] == r1[a] | r1[b]: count += 1
	elif 'borr' in ops[op]: ops[op].remove('borr')

	# bori
	if r2[c] == r1[a] | b: count += 1
	elif 'bori' in ops[op]: ops[op].remove('bori')

	# setr
	if r2[c] == r1[a]: count += 1
	elif 'setr' in ops[op]: ops[op].remove('setr')

	# seti
	if r2[c] == a: count += 1
	elif 'seti' in ops[op]: ops[op].remove('seti')

	# gtir
	t = 1 if a > r1[b] else 0
	if r2[c] == t: count += 1
	elif 'gtir' in ops[op]: ops[op].remove('gtir')

	# gtri
	t = 1 if r1[a] > b else 0
	if r2[c] == t: count += 1
	elif 'gtri' in ops[op]: ops[op].remove('gtri')

	# gtrr
	t = 1 if r1[a] > r1[b] else 0
	if r2[c] == t: count += 1
	elif 'gtrr' in ops[op]: ops[op].remove('gtrr')

	# eqir
	t = 1 if a == r1[b] else 0
	if r2[c] == t: count += 1
	elif 'eqir' in ops[op]: ops[op].remove('eqir')

	# eqri
	t = 1 if r1[a] == b else 0
	if r2[c] == t: count += 1
	elif 'eqri' in ops[op]: ops[op].remove('eqri')

	# eqrr
	t = 1 if r1[a] == r1[b] else 0
	if r2[c] == t: count += 1
	elif 'eqrr' in ops[op]: ops[op].remove('eqrr')

	return count

def execute(opmap, machine_code, r1):
	n, a, b, c = machine_code
	mnemonic = opmap[n]

	r2 = r1[:]

	if   mnemonic == 'addr':
		r2[c] = r1[a] + r1[b]

	elif mnemonic == 'addi':
		r2[c] = r1[a] + b

	elif mnemonic == 'mulr':
		r2[c] = r1[a] * r1[b]

	elif mnemonic == 'muli':
		r2[c] = r1[a] * b

	elif mnemonic == 'banr':
		r2[c] = r1[a] & r1[b]

	elif mnemonic == 'bani':
		r2[c] = r1[a] & b

	elif mnemonic == 'borr':
		r2[c] = r1[a] | r1[b]

	elif mnemonic == 'bori':
		r2[c] = r1[a] | b

	elif mnemonic == 'setr':
		r2[c] = r1[a]

	elif mnemonic == 'seti':
		r2[c] = a

	elif mnemonic == 'gtir':
		r2[c] = 1 if a > r1[b] else 0

	elif mnemonic == 'gtri':
		r2[c] = 1 if r1[a] > b else 0

	elif mnemonic == 'gtrr':
		r2[c] = 1 if r1[a] > r1[b] else 0

	elif mnemonic == 'eqir':
		r2[c] = 1 if a == r1[b] else 0

	elif mnemonic == 'eqri':
		r2[c] = 1 if r1[a] == b else 0

	elif mnemonic == 'eqrr':
		r2[c] = 1 if r1[a] == r1[b] else 0

	return r2

def simplify(ops):
	definitive = {}

	while len(definitive) != 16:
		added = []
		for num, candidates in ops.items():
			if len(candidates) == 1:
				assert num not in definitive

				definitive[num] = candidates.pop()
				added.append(num)

		for k in added:
			ops.pop(k)
			op = definitive[k]

			for kk in ops:
				if op in ops[kk]:
					ops[kk].remove(op)

					if len(ops[kk]) == 0:
						ops.pop(kk)

	return definitive

names = [
	'addr',
	'addi',
	'mulr',
	'muli',
	'banr',
	'bani',
	'borr',
	'bori',
	'setr',
	'seti',
	'gtir',
	'gtri',
	'gtrr',
	'eqir',
	'eqri',
	'eqrr'
]

ops = {}

for op in range(16):
	ops[op] = set(names[:])

data = fin.read().split('\n\n\n\n')
sims = data[0].split('\n\n')

ans = 0

for s in sims:
	before, op, after = s.split('\n')

	before = eval(before[before.find(':')+1:])
	op     = list(map(int, op.split()))
	after  = eval(after[after.find(':')+1:])

	if simulate(before, op, after) >= 3:
		ans += 1

advent.submit_answer(1, ans)

ok = simplify(ops)

for k, o in ok.items():
	print(k, o)

program = list(map(lambda l: list(map(int, l.split())), data[1].strip().split('\n')))

regs = [0] * 4

for instr in program:
	regs = execute(ok, instr, regs)

ans2 = regs[0]

advent.submit_answer(2, ans2)
