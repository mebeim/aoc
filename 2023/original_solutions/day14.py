#!/usr/bin/env python3

from utils.all import *

def move(beams, grid, dr, dc):
	newgrid = deepcopy(beams)

	if dr == -1:
		order = sorted(grid)
	elif dr == 1:
		order = sorted(grid, reverse=True)
	elif dc == 1:
		order = sorted(grid, key=lambda rc: rc[::-1], reverse=True)
	elif dc == -1:
		order = sorted(grid, key=lambda rc: rc[::-1])

	for r, c in order:
		newr, newc = r + dr, c + dc
		while 0 <= newr < H and 0 <= newc < W and (newr, newc) not in newgrid:
			newr += dr
			newc += dc

		x = (newr - dr, newc - dc)
		assert x not in newgrid
		newgrid.add(x)

	return newgrid - beams


def p2(beams, grid):
	dirs = [(-1, 0), (0, -1), (1, 0), (0, 1)]
	seen = {frozenset(grid): 0}
	revseen = {0: frozenset(grid)}

	for i in range(1, 1000000000):
		for dr, dc in dirs:
			grid = move(beams, grid, dr, dc)

		k = frozenset(grid)
		if k in seen:
			break

		seen[k] = i
		revseen[i] = k

	cycle_start = seen[k]
	cycle_len = i - cycle_start
	offset = i - cycle_len
	remaining = 1000000000 - cycle_start
	final = remaining % cycle_len + offset

	return sum(map(lambda rc: H - rc[0], revseen[final]))


advent.setup(2023, 14)
fin = advent.get_input()
rawgrid = read_lines(fin)

ans = ans1 = ans2 = 0
H, W = len(rawgrid), len(rawgrid[0])

beams = set()
grid = set()

for r, row in enumerate(rawgrid):
	for c, char in enumerate(row):
		if char == '#':
			beams.add((r, c))
		elif char == 'O':
			grid.add((r, c))

g = move(beams, grid, -1, 0)
ans1 = sum(map(lambda rc: H - rc[0], g))
advent.print_answer(1, ans1)

ans2 = p2(beams, grid)
advent.print_answer(2, ans2)
