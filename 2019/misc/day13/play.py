#!/usr/bin/env python3
#
# Intcode arcade game emulator using curses.
#
# Takes the name of an intcode program which is a valid puzzle input from AoC
# 2019 day 13 and runs the arcade game on the terminal while auto-playing.
#
# (C) 2019 Marco Bonelli -- https://github.com/mebeim/aoc
#

import os
import sys
import curses
from time import sleep
from collections import defaultdict

# Hack to import modules in parent folders.
from os.path import dirname as dn, realpath as rp
sys.path.append(dn(dn(dn(rp(__file__)))))

from lib.intcode import IntcodeVM

EMPTY, WALL, BLOCK, PADDLE, BALL = range(5)
TILE_MAP = {EMPTY: ' ', WALL: '+', BLOCK: '#', PADDLE: '=', BALL: 'o'}
REV_TILE_MAP = {v: k for k, v in TILE_MAP.items()}

def build_grid(screen):
	minx = min(x for x, _ in screen)
	maxx = max(x for x, _ in screen)
	miny = min(y for _, y in screen)
	maxy = max(y for _, y in screen)

	height = maxy - miny + 1
	width = maxx - minx + 1
	grid = [[' '] * width for _ in range(height)]

	for y in range(height):
		for x in range(width):
			grid[y][x] = TILE_MAP[screen[x + minx, y + miny]]

	return grid

def display(curses_pad, grid, score):
	s = '\n'.join(''.join(grid[y]) for y in range(len(grid)))
	s += '\n Score: {}\n'.format(score)

	try:
		curses_pad.move(0, 0)
		curses_pad.addstr(s)
		curses_pad.refresh(0, 0, 0, 0, len(grid), len(grid[0]))
	except:
		return False

	sleep(0.05)
	return True

def game(stdscr, program):
	stdscr.clear()
	curses.curs_set(False)

	program[0] = 2
	vm = IntcodeVM(program)
	screen = {}
	n_tiles = 0

	while True:
		x, y, tile = vm.run([0], resume=True, n_out=3)

		if (x, y) != (-1, 0):
			screen[x, y] = tile

		if len(screen) == n_tiles:
			break

		n_tiles = len(screen)

	grid = build_grid(screen)
	pad  = curses.newpad(100, 100)
	del screen

	make_move = True
	redraw    = False
	paddle_x  = 0
	inp       = [0]
	score     = 0

	while True:
		out = vm.run(inp, resume=True, n_out=3)
		if not out:
			break

		x, y, tile = out

		if (x, y) == (-1, 0):
			score = tile
		else:
			if tile in (BALL, PADDLE) and REV_TILE_MAP[grid[y][x]] == EMPTY:
				redraw = True

			grid[y][x] = TILE_MAP[tile]

			if tile == BALL and make_move:
				if x > paddle_x:
					inp = [1]
				elif x < paddle_x:
					inp = [-1]

				make_move = False
			elif tile == PADDLE and not make_move:
				paddle_x = x
				make_move = True

		if redraw:
			redraw = False
			ok = display(pad, grid, score)

			if not ok:
				return 1

	sleep(1)
	return 0

if __name__ == '__main__':
	if len(sys.argv) != 2:
		sys.stderr.write('Usage: {} valid_day13_input.txt\n'.format(sys.argv[0]))
		sys.stderr.write('Run on a valid AoC 2019 day 13 input!\n')
		sys.exit(1)

	with open(sys.argv[1]) as fin:
		program = list(map(int, fin.read().split(',')))

	ret = curses.wrapper(game, program)

	if ret == 1:
		sys.stderr.write('Terminal too small!\n')

	sys.exit(ret)
