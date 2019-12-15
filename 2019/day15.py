#!/usr/bin/env python3

import advent
from utils import *

advent.setup(2019, 15)
fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

# I'm not even bothering to try and clean this mess LOL

NORTH, SOUTH, WEST, EAST = 1, 2, 3, 4
HITWALL, MOVED, FOUNDOXYGEN = 0, 1, 2

from lib.intcode import IntcodeVM
prog = get_ints(fin, True)
vm = IntcodeVM(prog)

def path_to_moves(path):
	for a, b in zip(path, path[1:]):
		if b[0] > a[0]:
			yield EAST
		elif b[0] < a[0]:
			yield WEST
		elif b[1] > a[1]:
			yield NORTH
		elif b[1] < a[1]:
			yield SOUTH

def walk(path, stop_if_oxygen=False):
	vm.reset()

	dst = None

	for dst, mv in zip(path[1:], path_to_moves(path)):
		out = vm.run([mv], resume=1, n_out=1)

		if not out:
			break

		res = out[0]
		# log('{} -> {} -> {}\n', mv, dst, 'WMO'[res])

		if res == HITWALL:
			return res, dst
		elif stop_if_oxygen and res == FOUNDOXYGEN:
			print('OXYGEN', dst)
			print('OXYGEN', dst)
			print('OXYGEN', dst)
			print('OXYGEN', dst)
			print('OXYGEN', dst)
			print('OXYGEN', dst)
			return res, dst

	assert dst is not None

	return MOVED, dst

def build_grid(walls):
	minx = min(x for x, _ in walls)
	maxx = max(x for x, _ in walls)
	miny = min(y for _, y in walls)
	maxy = max(y for _, y in walls)

	height = maxy - miny + 1
	width = maxx - minx + 1
	grid = [[' '] * width for _ in range(height)]

	for y in range(height):
		for x in range(width):
			cell = (minx + x, miny + y)
			if cell == OXYGEN:
				grid[y][x] = 'x'
			elif cell == (0,0):
				grid[y][x] = '@'
			else:
				grid[y][x] = '█' if cell in walls else ' '

	return grid

import sys
import pickle
from copy import deepcopy

eprint('restoring walls')

bkp_walls = None

try:
	with open('walls.pkl', 'rb') as f:
		bkp_walls = pickle.load(f)
except:
	eprint('failed restore starting new')


# PART 2
OXYGEN = (-20, -14)
walls = deepcopy(bkp_walls) if bkp_walls is not None else set()
grid = build_grid(walls)
dump_char_matrix(grid)

G = nx.Graph()
startpos = None

for y in range(len(grid)):
	for x, cell in enumerate(grid[y]):
		if cell == '█':
			continue

		xy = (x, y)

		if cell == 'x':
			startpos = xy

		neigh = (
			(x+1, y),
			(x-1, y),
			(x, y+1),
			(x, y-1)
		)

		for n in neigh:
			x2, y2 = n
			if 0 <= x2 < len(grid[0]) and 0 <= y2 < len(grid):
				if grid[y2][x2] != '█':
					G.add_edge(xy, n)

ans = max(nx.shortest_path_length(G, startpos, node) for node in G)
advent.submit_answer(2, ans)

# PART 2
sys.exit(0)


minx, maxx = -100, 100
miny, maxy = -100, 100
tosee = set()

G = nx.Graph()
eprint('building graph')

for x in range(minx, maxx+1):
	for y in range(miny, maxy+1):
		xy = (x, y)

		if xy not in walls:
			G.add_node(xy)
			tosee.add(xy)
		else:
			continue

		neigh = (
			(x+1, y),
			(x-1, y),
			(x, y+1),
			(x, y-1)
		)

		for n in neigh:
			if n not in walls:
				G.add_edge(xy, n)

	log('  {}   \r', x)

eprint('graph done')

src = (0, 0)

# PART 1
# FOUND OXYGEN
# OXYGEN = (-20, -14)
# tosee = set([OXYGEN])

tot = len(tosee)

try:
	for i, dst in enumerate(tosee, 1):
		log('{:04d}/{} check {}       \r', i, tot, dst)
		done = False

		if src == dst:
			continue

		while not done:
			try:
				path = nx.shortest_path(G, src, dst)
			except nx.exception.NetworkXNoPath:
				break
			except nx.exception.NodeNotFound:
				break

			log('{:04d}/{} going from {} to {}... ', i, tot, src, dst)

			# part 1
			#res, lastpos = walk(path, stop_if_oxygen=True)

			# part 2
			res, lastpos = walk(path, stop_if_oxygen=False)

			eprint('WMO'[res], lastpos)

			if res == HITWALL:
				G.remove_node(lastpos)
				walls.add(lastpos)
			elif res == FOUNDOXYGEN:
				done = True
				ans = len(path) - 1
				break
			elif res == MOVED:
				break

except KeyboardInterrupt:
	eprint('stopping')
	pass

eprint()

if len(walls) > len(bkp_walls):
	log('saving {} walls\n', len(walls))

	with open('walls.pkl', 'wb') as f:
		pickle.dump(walls, f)

# advent.submit_answer(1, ans)
