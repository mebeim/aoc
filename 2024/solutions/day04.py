#!/usr/bin/env python3

import sys


def grid_char(r, c):
	global GRID, WIDTH, HEIGHT

	if 0 <= r < HEIGHT and 0 <= c < WIDTH:
		return GRID[r][c]
	return ''


def count_xmas(r, c):
	global GRID

	if GRID[r][c] != 'X':
		return 0

	deltas = ((0, 1), (0, -1), (1, 0), (-1, 0), (1, 1), (1, -1), (-1, 1), (-1, -1))
	count = 0

	for dr, dc in deltas:
		rr, cc = r, c

		for i in range(3):
			rr += dr
			cc += dc
			if grid_char(rr, cc) != 'MAS'[i]:
				break
		else:
			count += 1

	return count


def check_xmas(r, c):
	global GRID

	if GRID[r][c] != 'A':
		return False

	a = grid_char(r - 1, c - 1) + grid_char(r + 1, c + 1)
	if a != 'MS' and a != 'SM':
		return False

	b = grid_char(r + 1, c - 1) + grid_char(r - 1, c + 1)
	return b == 'MS' or b == 'SM'


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

GRID = fin.read().splitlines()
HEIGHT, WIDTH = len(GRID), len(GRID[0])

total1 = sum(count_xmas(r, c) for r in range(HEIGHT) for c in range(WIDTH))
print('Part 1:', total1)

total2 = sum(check_xmas(r, c) for r in range(1, HEIGHT - 1) for c in range(1, WIDTH - 1))
print('Part 2:', total2)
