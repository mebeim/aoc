#!/usr/bin/env python3

import sys
from itertools import product
from operator import itemgetter
from collections import defaultdict, deque

def fall(space, brick_id, ax, ay, az, bx, by, bz):
	below = set()

	for z in range(az, -1, -1):
		for x, y in product(range(ax, bx + 1), range(ay, by + 1)):
			coords = (x, y, z)
			if coords in space:
				below.add(space[coords])

		if below:
			break

	delta = az - z - 1
	az -= delta
	bz -= delta

	for coords in product(range(ax, bx + 1), range(ay, by + 1), range(az, bz + 1)):
		space[coords] = brick_id

	return below

def simulate(bricks):
	bricks.sort(key=itemgetter(2))
	space = {}
	supports = {}

	for brick_id, brick in enumerate(bricks):
		supports[brick_id] = fall(space, brick_id, *brick)

	supported_by = defaultdict(set)
	for brick, below in supports.items():
		for b in below:
			supported_by[b].add(brick)

	return supports, supported_by

def find_removable(supports):
	removable = set(range(len(bricks)))

	for below in supports.values():
		if len(below) == 1:
			removable.discard(*below)

	return removable

def count_falling(supports, supported_by, root_brick):
	q = deque([root_brick])
	falling = set()

	while q:
		brick = q.popleft()
		falling.add(brick)

		for supporter in supported_by[brick]:
			if all(s in falling for s in supports[supporter]):
				q.append(supporter)

	return len(falling) - 1


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1], 'r') if len(sys.argv) > 1 else sys.stdin

bricks = []
with fin:
	for line in fin:
		a, b = line.split('~')
		bricks.append((*map(int, a.split(',')), *map(int, b.split(','))))

supports, supported_by = simulate(bricks)
removable = find_removable(supports)
n_removable = len(removable)

print('Part 1:', n_removable)


tot_falling = 0
for brick_id in range(len(bricks)):
	if brick_id not in removable:
		tot_falling += count_falling(supports, supported_by, brick_id)

print('Part 2:', tot_falling)
