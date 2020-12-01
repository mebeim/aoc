#!/usr/bin/env python3

from utils.all import *
import sys

advent.setup(2019, 15)
fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

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
			return res, dst

	assert dst is not None

	return MOVED, dst

def build_grid(walls, oxygen_position, my_position):
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
			if cell == oxygen_position:
				grid[y][x] = 'x'
			elif cell == my_position:
				grid[y][x] = '@'
			else:
				grid[y][x] = '█' if cell in walls else ' '

	return grid

# import pickle
# from copy import deepcopy
# eprint('restoring walls')
# bkp_walls = set()
# try:
# 	with open('walls.pkl', 'rb') as f:
# 		bkp_walls = pickle.load(f)
# except:
# 	eprint('failed restore starting new')
# walls = deepcopy(bkp_walls) if bkp_walls else set()

walls = set()

minx, maxx = -50, 50
miny, maxy = -50, 50
tosee = set()

G = nx.Graph()
# eprint('building graph')

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

	# log('  {}   \r', x)

# eprint('graph done')

src = (0, 0)
tot = len(tosee)
oxygen_found = False

try:
	for i, dst in enumerate(tosee, 1):
		log('{:04d}/{} check {}                                 \r', i, tot, dst)

		if src == dst:
			continue

		while True:
			try:
				path = nx.shortest_path(G, src, dst)
			except nx.exception.NetworkXNoPath:
				break
			except nx.exception.NodeNotFound:
				break

			log('{:04d}/{} going from {} to {}... ', i, tot, src, dst)

			res, lastpos = walk(path, stop_if_oxygen=(not oxygen_found))
			log('{} {}      \r', 'WMO'[res], lastpos)

			if res == HITWALL:
				G.remove_node(lastpos)
				walls.add(lastpos)
			elif res == FOUNDOXYGEN:
				eprint()
				eprint('found oxygen')
				oxygen_found = True
				oxygen_position = lastpos
				oxygen_path = nx.shortest_path(G, src, oxygen_position)
				oxygen_distance = len(oxygen_path) - 1
				advent.submit_answer(1, oxygen_distance)
				break
			elif res == MOVED:
				break

except KeyboardInterrupt:
	eprint('stopping')
	pass

eprint()

# if len(walls) > len(bkp_walls):
# 	log('saving {} walls\n', len(walls))

# 	with open('walls.pkl', 'wb') as f:
# 		pickle.dump(walls, f)

# advent.submit_answer(1, ans)

# PART 2
my_position = (0, 0)
grid = build_grid(walls, oxygen_position, my_position)
dump_char_matrix(grid)

G = nx.Graph()
startpos = None

for y in range(len(grid)):
	for x, cell in enumerate(grid[y]):
		if cell == '█':
			continue

		xy = (x, y)

		if cell == 'x': # oxygen
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
