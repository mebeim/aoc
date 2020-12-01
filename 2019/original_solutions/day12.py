#!/usr/bin/env python3

from utils.all import *

# fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

moons =  [
	[-7, 17, -11],
	[9, 12, 5],
	[-9, 0, -4],
	[4, 6, 0]
]

vels = [
	[0,0,0],
	[0,0,0],
	[0,0,0],
	[0,0,0]
]

for _ in range(1000):
	accels = [
		[0,0,0],
		[0,0,0],
		[0,0,0],
		[0,0,0]
	]

	for i in range(4):
		for j in range(4):
			if i == j:
				continue

			if moons[i][0] < moons[j][0]:
				accels[i][0] += 1
				accels[j][0] -= 1

			if moons[i][1] < moons[j][1]:
				accels[i][1] += 1
				accels[j][1] -= 1

			if moons[i][2] < moons[j][2]:
				accels[i][2] += 1
				accels[j][2] -= 1

	# for i, (m, v, a) in enumerate(zip(moons, vels, accels)):
	# 	print('{:10d} {:10d} {:10d} | {:10d} {:10d} {:10d} | {:10d} {:10d} {:10d}'.format(*m, *v, *a))
	# print('-------------------'*6)

	for i in range(4):
		vels[i][0] += accels[i][0]
		vels[i][1] += accels[i][1]
		vels[i][2] += accels[i][2]

		moons[i][0] += vels[i][0]
		moons[i][1] += vels[i][1]
		moons[i][2] += vels[i][2]

pot = [sum(map(abs, m)) for m in moons]
kin = [sum(map(abs, m)) for m in vels]
tot = sum(p * k for p, k in zip(pot, kin))

advent.submit_answer(1, tot)


moons = [
	[-7, 17, -11],
	[9, 12, 5],
	[-9, 0, -4],
	[4, 6, 0]
]

vels = [
	[0,0,0],
	[0,0,0],
	[0,0,0],
	[0,0,0]
]

history = [set() for _ in range(3)]
periods = [0] * 3
found = [False] * 3
steps = 0

while not all(found):
	# if steps % 10000 == 0:
	# 	print(steps, periods)

	for dim in range(3):
		x = tuple((m[dim], v[dim]) for m, v in zip(moons, vels))

		if not found[dim] and x in history[dim]:
			periods[dim] = steps
			found[dim] = True
		else:
			history[dim].add(x)

	accels = [
		[0,0,0],
		[0,0,0],
		[0,0,0],
		[0,0,0]
	]

	for i in range(4):
		for j in range(4):
			if i == j:
				continue

			if moons[i][0] < moons[j][0]:
				accels[i][0] += 1
				accels[j][0] -= 1

			if moons[i][1] < moons[j][1]:
				accels[i][1] += 1
				accels[j][1] -= 1

			if moons[i][2] < moons[j][2]:
				accels[i][2] += 1
				accels[j][2] -= 1



	for i in range(4):
		vels[i][0] += accels[i][0]
		vels[i][1] += accels[i][1]
		vels[i][2] += accels[i][2]

		moons[i][0] += vels[i][0]
		moons[i][1] += vels[i][1]
		moons[i][2] += vels[i][2]

	steps += 1

# print(periods)

from math import gcd

lcm = periods[0]
for i in periods[1:]:
  lcm = lcm*i//gcd(lcm, i)

# 2988031200 not right
advent.submit_answer(2, lcm)
