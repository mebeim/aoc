#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 4)

fin = advent.get_input()
grid = read_char_matrix(fin)

ans1 = ans2 = 0


def direc(grid, r, c, dr, dc):
	word = ''

	rr, cc = r, c
	for i in range(4):
		rr, cc = r + i * dr, c + i * dc
		if rr < 0 or cc < 0 or rr >= len(grid) or cc >= len(grid[0]):
			continue

		word += grid[rr][cc]

	return word == 'XMAS'

def gridchar(grid, r, c):
	if r < 0 or c < 0 or r >= len(grid) or c >= len(grid[0]):
		return ''
	return grid[r][c]

def mas(grid, r, c):
	a = gridchar(grid, r - 1, c - 1)
	a += gridchar(grid, r, c)
	a += gridchar(grid, r + 1, c + 1)

	b = gridchar(grid, r + 1, c - 1)
	b += gridchar(grid, r, c)
	b += gridchar(grid, r - 1, c + 1)

	return a in ('MAS', 'SAM') and b in ('MAS', 'SAM')


for r, row in enumerate(grid):
	for c, char in enumerate(row):
		ans1 += direc(grid, r, c, 0, 1) \
			+ direc(grid, r, c, 0, -1) \
			+ direc(grid, r, c, 1, 0) \
			+ direc(grid, r, c, -1, 0) \
			+ direc(grid, r, c, 1, 1) \
			+ direc(grid, r, c, 1, -1) \
			+ direc(grid, r, c, -1, 1) \
			+ direc(grid, r, c, -1, -1)

advent.print_answer(1, ans1)


for r, row in enumerate(grid):
	for c, char in enumerate(row):
		ans2 += mas(grid, r, c)

advent.print_answer(2, ans2)
