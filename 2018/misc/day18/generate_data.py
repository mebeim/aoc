#!/usr/bin/env python3

import os
import sys
import copy
import pickle

def adj(curgrid, x, y):
	for dx, dy in ((-1,-1), (-1,0), (-1,1), (0,-1), (0,1), (1,-1), (1,0), (1,1)):
		nx, ny = x + dx, y + dy

		if 0 <= nx < gridh and 0 <= ny < gridw:
			yield curgrid[nx][ny]

def transform(curgrid, x, y):
	nempty = ntrees = nlumb = 0
	cell = curgrid[x][y]

	for a in adj(curgrid, x, y):
		if   a == EMPTY: nempty += 1
		elif a == TREE : ntrees += 1
		elif a == LUMB : nlumb  += 1

	if   cell == EMPTY: return TREE if ntrees >= 3 else EMPTY
	elif cell == TREE : return LUMB if nlumb >= 3 else TREE
	elif cell == LUMB : return LUMB if nlumb >= 1 and ntrees >= 1 else EMPTY

def gen(startgrid, n):
	if n < 1:
		return

	grid = copy.deepcopy(startgrid)
	yield grid

	for _ in range(n-1):
		newgrid = copy.deepcopy(grid)

		for x in range(gridh):
			for y in range(gridw):
				newgrid[x][y] = transform(grid, x, y)

		grid = newgrid
		yield grid


EMPTY, TREE, LUMB = range(3)
CHARMAP = dict(zip('.|#', range(3)))

if len(sys.argv[1:]) != 2:
	sys.stderr.write('Usage {} inpt_file.in N\n'.format(sys.argv[0]))
	sys.exit(1)

if not os.path.isdir('data'):
	os.mkdir('data')

with open(sys.argv[1]) as f:
	grid  = [[CHARMAP[c] for c in l.strip()] for l in f]

n     = int(sys.argv[2])
gridh = len(grid)
gridw = len(grid[0])

for i, g in enumerate(gen(grid, n)):
	sys.stderr.write('Generating grid #{}...\r'.format(i))
	sys.stderr.flush()

	with open('data/grid_{:04d}.pkl'.format(i), 'wb') as f:
		pickle.dump(g, f, protocol=4)

sys.stderr.write('\nDone! All data generated.\n')
sys.stderr.flush()
