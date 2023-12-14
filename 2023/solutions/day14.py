#!/usr/bin/env python3

import sys

def rotate_90(coords, height):
	return set((c, height - r - 1) for r, c in coords)

def move(spheres, cubes):
	new_spheres = set()

	for r, c in sorted(spheres):
		r -= 1
		while r >= 0 and (r, c) not in cubes and (r, c) not in new_spheres:
			r -= 1

		new_spheres.add((r + 1, c))

	return new_spheres

def spin(spheres, cubes, height, iterations):
	seen = {frozenset(spheres): 0}

	cached_cubes = [cubes]
	for _ in range(3):
		cached_cubes.append(rotate_90(cached_cubes[-1], height))

	for i in range(1, iterations + 1):
		for cubes in cached_cubes:
			spheres = rotate_90(move(spheres, cubes), height)

		key = frozenset(spheres)
		if key in seen:
			break

		seen[key] = i
		seen[i]   = key

	offset    = seen[key]
	cycle_len = i - offset
	remaining = iterations - offset
	final     = remaining % cycle_len + offset

	return sum(map(lambda rc: height - rc[0], seen[final]))


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

grid    = fin.read().splitlines()
height  = len(grid)
width = len(grid[0]) # test
cubes   = set()
spheres = set()

for r, row in enumerate(grid):
	for c, char in enumerate(row):
		if char == '#':
			cubes.add((r, c))
		elif char == 'O':
			spheres.add((r, c))

total1 = sum(map(lambda rc: height - rc[0], move(spheres, cubes)))
print('Part 1:', total1)

total2 = spin(spheres, cubes, height, 1000000000)
print('Part 2:', total2)
