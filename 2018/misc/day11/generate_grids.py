#!/usr/bin/env python3

import os
import sys
import pickle

def fuel(serial_no, x, y):
	rid = x + 10
	powlevel = ((((rid*y + serial_no)*rid) // 100) % 10) - 5
	return powlevel

def get_power(grid, xy, m):
	s = 0
	x, y = xy
	for j in range(y, y+m):
		for i in range(x, x+m):
			s += grid[j][i]
	return s

def run(serial_no):
	grid = []
	for j in range(300+1):
		grid.append([])
		for i in range(300+1):
			grid[j].append(fuel(serial_no, i, j))

	p1x, p1y = max(((x, y) for x in range(1, 301-3+1) for y in range(1, 301-3+1)), key=lambda xy: get_power(grid, xy, 3))
	p1p = get_power(grid, (p1x, p1y), 3)

	maxp = -999999
	maxpsize = 0
	maxans = (-1, -1)

	prevp = maxp
	consecutive_desc = 0

	for sz in range(1, 301):
		sys.stderr.write('Serial {}: size {}... '.format(serial_no, sz))

		ans = max(((x, y) for x in range(1, 301-sz+1) for y in range(1, 301-sz+1)), key=lambda xy: get_power(grid, xy, sz))
		p = get_power(grid, ans, sz)

		sys.stderr.write('P{} = {}'.format(ans, p))

		if p > maxp:
			maxp = p
			maxpsize = sz
			maxans = ans

			sys.stderr.write(' -> MAX!')

		sys.stderr.write('          \r')
		sys.stderr.flush()

		if p < prevp:
			consecutive_desc += 1
		else:
			consecutive_desc = 0

		if consecutive_desc >= 5:
			break

		prevp = p

	sys.stderr.write('Serial {}: max 3x3 @ P{} = {}, {}x{} @ P{} = {}        \n'.format(serial_no, (p1x, p1y), p1p, maxpsize, maxpsize, maxans, maxp))
	sys.stderr.flush()

	# sys.stdout.write('Serial {}: max 3x3 @ P{} = {}, {}x{} @ P{} = {}        \n'.format(serial_no, (p1x, p1y), p1p, maxpsize, maxpsize, maxans, maxp))
	# sys.stdout.flush()

	return grid, (p1x, p1y, 3), (maxans[0], maxans[1], maxpsize)

######################################################################

if not os.path.isdir('grids'):
	os.mkdir('grids')

tot = 500

sys.stderr.write('Generating first {} grids... this will take a while!\n'.format(tot))
sys.stderr.flush()

for n in range(tot):
	grid, p1, p2 = run(n)

	with open('grids/grid_{:03d}.pkl'.format(n), 'wb') as f:
		pickle.dump({
			'grid': grid,
			'p1': p1,
			'p2': p2
		}, f, protocol=4)
