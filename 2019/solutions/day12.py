#!/usr/bin/env python3

import sys
import re
from math import gcd
from functools import reduce
from collections import namedtuple
from itertools import combinations, count

def lcm(a, b):
	return abs(a * b) // gcd(a, b)


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

exp = re.compile(r'-?\d+')
initial_positions = [list(map(int, exp.findall(line))) for line in fin]

Moon = namedtuple('Moon', ['pos', 'vel'])
moons = [Moon(pos.copy(), [0, 0, 0]) for pos in initial_positions]

for step in range(1000):
	for moon1, moon2 in combinations(moons, 2):
		for dim in range(3):
			if moon2.pos[dim] > moon1.pos[dim]:
				moon1.vel[dim] += 1
				moon2.vel[dim] -= 1
			elif moon2.pos[dim] < moon1.pos[dim]:
				moon1.vel[dim] -= 1
				moon2.vel[dim] += 1

	for moon in moons:
		for dim in range(3):
			moon.pos[dim] += moon.vel[dim]

potential = (sum(map(abs, m.pos)) for m in moons)
kinetic   = (sum(map(abs, m.vel)) for m in moons)
total     = sum(p * k for p, k in zip(potential, kinetic))

print('Part 1:', total)


periods = []
start = step + 1

for dim in range(3):
	for period in count(start):
		if all(m.vel[dim] == 0 for m in moons):
			break

		for moon1, moon2 in combinations(moons, 2):
			if moon2.pos[dim] > moon1.pos[dim]:
				moon1.vel[dim] += 1
				moon2.vel[dim] -= 1
			elif moon2.pos[dim] < moon1.pos[dim]:
				moon1.vel[dim] -= 1
				moon2.vel[dim] += 1

		for moon in moons:
			moon.pos[dim] += moon.vel[dim]

	periods.append(period)

total_steps = 2 * reduce(lcm, periods, 1)
print('Part 2:', total_steps)
