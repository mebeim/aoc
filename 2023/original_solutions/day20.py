#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 20)
fin = advent.get_input()
lines = read_lines(fin)

def go():
	q = deque([('button', 'broadcaster', False)])
	nlo = nhi = 0

	while q:
		sender, receiver, pulse = q.popleft()
		# print(sender, '-high->' if pulse else '-low->', receiver)

		if not pulse:
			nlo += 1
		else:
			nhi += 1

		if receiver in flops:
			if not pulse:
				state = flops[receiver] = not flops[receiver]

				for y in g[receiver]:
					q.append((receiver, y, state))
		elif receiver in conj:
			conj[receiver][sender] = pulse
			# print(*conj[receiver].items())
			state = not all(conj[receiver].values())

			for y in g[receiver]:
				q.append((receiver, y, state))
		else:
			# assert receiver == 'broadcaster', receiver
			if receiver in g:
				for y in g[receiver]:
					q.append((receiver, y, pulse))

	return nlo, nhi

def go2():
	rx_prev = None
	useful = set()

	for a, bs in g.items():
		if bs == ['rx']:
			rx_prev = a
			break

	assert rx_prev in conj
	print(f'{rx_prev=}')

	for a, bs in g.items():
		if rx_prev in bs:
			useful.add(a)
			assert a in conj

	print(f'{useful=}')

	# for u in useful:
	# 	print(u, conj[u])

	for i in count(1):
		q = deque([('button', 'broadcaster', False)])

		while q:
			sender, receiver, pulse = q.popleft()
			if not pulse:
				if receiver in useful:
					print(receiver, i)
					# stop manually LOL

			if receiver in flops:
				if not pulse:
					state = flops[receiver] = not flops[receiver]

					for y in g[receiver]:
						q.append((receiver, y, state))
			elif receiver in conj:
				conj[receiver][sender] = pulse
				state = not all(conj[receiver].values())

				for y in g[receiver]:
					q.append((receiver, y, state))
			else:
				if receiver in g:
					for y in g[receiver]:
						q.append((receiver, y, pulse))


flops = {}
conj = {}
g = {}

for line in lines:
	a, b = line.split('->')
	a = a.strip()
	b = list(map(str.strip, b.strip().split(',')))
	# print(a, b)

	if a[0] == '%':
		flops[a[1:]] = False
		g[a[1:]] = b
	elif a[0] == '&':
		conj[a[1:]] = {}
		g[a[1:]] = b

		for bb in b:
			if bb in conj:
				conj[bb][a[1:]] = False
	else:
		assert a == 'broadcaster'
		g[a] = b

for a, bs in g.items():
	for b in bs:
		if b in conj:
			conj[b][a] = False

orig_flops = deepcopy(flops)
orig_conj = deepcopy(conj)

tota = totb = 0
for _ in range(1000):
	a, b = go()
	tota += a
	totb += b

ans1 = tota * totb
advent.print_answer(1, ans1)


flops = orig_flops
conj = orig_conj

# go2()
#
# Run go2() and stop manually, grab the first 4 values of the "useful" modules:
#
#   useful={'vk', 'dl', 'pm', 'ks'}
#   dl 3769 <---
#   pm 3833 <---
#   vk 3877 <---
#   ks 3917 <---
#   dl 7538
#   ...

ans2 = lcm(3769, 3833, 3877, 3917)
advent.print_answer(2, ans2)
