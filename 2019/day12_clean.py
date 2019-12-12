#!/usr/bin/env python3

import advent
import re
from fractions import gcd
from functools import reduce

def lcm(a, b):
	return abs(a * b) // gcd(a, b)


advent.setup(2019, 12, dry_run=True)
fin = advent.get_input()

rexp = re.compile(r'-?\d+')
moons = [list(map(int, rexp.findall(line))) for line in fin]

positions  = [m[:] for m in moons]
velocities = [[0] * 3 for _ in range(len(moons))]
pos_vel    = tuple(zip(positions, velocities))

for step in range(1000):
	for i, (p, v) in enumerate(pos_vel):
		for j, p2 in enumerate(positions):
			if i == j:
				continue

			for dim in range(3):
				if   p2[dim] > p[dim]: v[dim] += 1
				elif p2[dim] < p[dim]: v[dim] -= 1

	for i, (p, v) in enumerate(pos_vel):
		for dim in range(3):
			p[dim] += v[dim]

potential = (sum(map(abs, p)) for p in positions)
kinetic   = (sum(map(abs, v)) for v in velocities)
total     = sum(p * k for p, k in zip(potential, kinetic))

assert total == 7013
advent.submit_answer(1, total)


initial_states = []
for dim in range(3):
	initial_states.append(tuple((m[dim], 0) for m in moons))

periods = [0] * 3

while not all(periods):
	step += 1

	for dim in range(3):
		if not periods[dim]:
			cur_state = tuple((p[dim], v[dim]) for p, v in pos_vel)

			if cur_state == initial_states[dim]:
				periods[dim] = step

	for i, (p, v) in enumerate(pos_vel):
		for j, p2 in enumerate(positions):
			if i == j:
				continue

			for dim in range(3):
				if   p2[dim] > p[dim]: v[dim] += 1
				elif p2[dim] < p[dim]: v[dim] -= 1

	for i, (p, v) in enumerate(pos_vel):
		for dim in range(3):
			p[dim] += v[dim]

total_steps = reduce(lcm, periods, 1)

assert total_steps == 324618307124784
advent.submit_answer(2, total_steps)
