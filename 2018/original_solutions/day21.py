#!/usr/bin/env python3

from utils.all import *

advent.setup(2018, 21)
fin = advent.get_input()
# print(*fin)

##################################################

opcodes = {
	'addr': lambda r,a,b: r[a] + r[b],             #  0 addr
	'addi': lambda r,a,b: r[a] + b,                #  1 addi
	'mulr': lambda r,a,b: r[a] * r[b],             #  2 mulr
	'muli': lambda r,a,b: r[a] * b,                #  3 muli
	'banr': lambda r,a,b: r[a] & r[b],             #  4 banr
	'bani': lambda r,a,b: r[a] & b,                #  5 bani
	'borr': lambda r,a,b: r[a] | r[b],             #  6 borr
	'bori': lambda r,a,b: r[a] | b,                #  7 bori
	'setr': lambda r,a,b: r[a],                    #  8 setr
	'seti': lambda r,a,b: a,                       #  9 seti
	'gtir': lambda r,a,b: 1 if a > r[b] else 0,    # 10 gtir
	'gtri': lambda r,a,b: 1 if r[a] > b else 0,    # 11 gtri
	'gtrr': lambda r,a,b: 1 if r[a] > r[b] else 0, # 12 gtrr
	'eqir': lambda r,a,b: 1 if a == r[b] else 0,   # 13 eqir
	'eqri': lambda r,a,b: 1 if r[a] == b else 0,   # 14 eqri
	'eqrr': lambda r,a,b: 1 if r[a] == r[b] else 0 # 15 eqrr
}

def sim(r0value, max_same_instr):
	i = 0
	killed = False
	instrmap = defaultdict(int)
	regs = [r0value, 0, 0, 0, 0, 0]

	while 0 <= regs[ip] < eoc:
		if instrmap[regs[ip]] >= max_same_instr:
			killed = True
			break

		# log('{:12d} | ip {:2d}: {} {:8d} {:8d} {} | {:12d}{:8d}{:8d}{:8d}{:8d}{:13d}         \n', i, regs[ip], *prog[regs[ip]], *regs)

		mnemonic, a, b, c = prog[regs[ip]]
		regs[c] = opcodes[mnemonic](regs, a, b)

		instrmap[regs[ip]] += 1 # whoops, this is off by one every time
		regs[ip] += 1
		i += 1

	# log('\n')

	# log('------------------------\n')
	# dump_dict(instrmap, 'opcode {:2d} executed {} times')
	# log('------------------------\n')

	return killed, i

def sim_intelligent(r0value, threshold):
	i    = 0
	regs = [r0value, 0, 0, 0, 0, 0]
	unique_targets = set()
	last_unique_target = -1
	time_since_last_unique_target = 0

	while 0 <= regs[ip] < eoc:
		if regs[ip] == 19:
			r4 = regs[4]
			x = r4 // 256
			regs[3] = x
			regs[2] = x + 1

		elif regs[ip] == 28:
			target = regs[5]

			if target in unique_targets:
				# log('#' * 50 + ' Repeated: {} ' + '#' * 50 + '\n', target)

				time_since_last_unique_target += 1
			else:
				# log('_' * 50 + ' First time I see: {} ' + '_' * 50 + '\n', target)

				last_unique_target = target
				time_since_last_unique_target = 0

			unique_targets.add(target)

			if time_since_last_unique_target > threshold:
				break

		# log('{:12d} | ip {:2d}: {} {:8d} {:8d} {} | {:12d}{:8d}{:8d}{:8d}{:8d}{:13d}         \n', i, regs[ip], *prog[regs[ip]], *regs)

		mnemonic, a, b, c = prog[regs[ip]]
		regs[c] = opcodes[mnemonic](regs, a, b)

		regs[ip] += 1
		i += 1

	# dump_iterable(sorted(targets))

	return last_unique_target


ip = 1
strings = get_lines(fin)
prog = []

for s in strings[1:]:
	mnemonic, a, b, c = s.strip().split(' ')
	a, b, c = map(int, (a, b, c))
	prog.append((mnemonic, a, b, c))

eoc = len(prog)

# Bruteforce? Why not, while I inspect the assembly...
r0_1 = 700674
r0_2 = 8610051
min_instr = 10e10
best_r0 = None

timer_start()

try:
	for r0 in range(r0_1, r0_2):
		if r0 % 10000 == 0:
			log('{:08d}/{:08d}\r', r0, r0_2)

		killed, instr = sim(r0, 500)

		if not killed:
			if instr < min_instr:
				log('new min: r0 = {} -> {}\n', r0, instr)
				min_instr = instr
				best_r0 = r0
except KeyboardInterrupt:
	pass

timer_lap()

# 700674 too low
# 8610051 too high
# 11850694 too high

# 3941014 lmao bruteforcing actually worked
advent.submit_answer(1, best_r0)

last_unique = sim_intelligent(-1, 10000000)
timer_lap()

# 1376005 too low
# 1394044 too low
advent.submit_answer(2, last_unique)
timer_stop()
