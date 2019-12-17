#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 17)
fin = advent.get_input()
TESTPLZ = any(a.lower() == 'test' for a in sys.argv[1:])
ftest = io.StringIO('''\
.#.
..#
###
''')

if TESTPLZ:
	fin = ftest
timer_start()

startgrid = get_char_matrix(fin)
cube = defaultdict(lambda: '.')

for x, row in enumerate(startgrid):
	for y, cell in enumerate(row):
		cube[x, y, 0] = cell

def neigh(cube, x, y, z):
	tot = 0
	for dx, dy, dz in product((-1, 0, 1), (-1, 0, 1), (-1, 0, 1)):
		if dx != 0 or dy != 0 or dz != 0:
			xx, yy, zz = (x + dx, y + dy, z + dz)
			if cube[xx, yy, zz] == '#':
				tot += 1
	return tot

def evolve(cube):
	new = deepcopy(cube)

	lox = min(map(itemgetter(0), cube.keys())) - 1
	loy = min(map(itemgetter(1), cube.keys())) - 1
	loz = min(map(itemgetter(2), cube.keys())) - 1
	hix = max(map(itemgetter(0), cube.keys())) + 2
	hiy = max(map(itemgetter(1), cube.keys())) + 2
	hiz = max(map(itemgetter(2), cube.keys())) + 2

	for x, y, z in product(range(lox, hix), range(loy, hiy), range(loz, hiz)):
		cell = cube[x, y, z]
		alive = neigh(cube, x, y, z)

		if cell == '#':
			if alive not in (2, 3):
				new[x, y, z] = '.'
		elif cell == '.':
			if alive == 3:
				new[x, y, z] = '#'

	return new

def dump(cube):
	eprint()
	grids = {}
	for (x, y, z), cell in cube.items():
		if z not in grids:
			grids[z] = [['.' for _ in range(10)] for __ in range(10)]
		grids[z][x][y] = cell

	for z in grids:
		eprint(f'z={z}')
		dump_char_matrix(grids[z])
	eprint()

for _ in range(6):
	# dump(cube)
	cube = evolve(cube)

# dump(cube)

ans = sum(x == '#' for x in cube.values())
advent.print_answer(1, ans)


def neigh4d(cube, x, y, z, w):
	tot = 0
	for dx, dy, dz, dw in product((-1, 0, 1), (-1, 0, 1), (-1, 0, 1), (-1, 0, 1)):
		if dx != 0 or dy != 0 or dz != 0 or dw != 0:
			xx, yy, zz, ww = (x + dx, y + dy, z + dz, w + dw)
			if cube[xx, yy, zz, ww] == '#':
				tot += 1
	return tot

def evolve4d(cube):
	new = deepcopy(cube)

	lox = min(map(itemgetter(0), cube.keys())) - 1
	loy = min(map(itemgetter(1), cube.keys())) - 1
	loz = min(map(itemgetter(2), cube.keys())) - 1
	low = min(map(itemgetter(3), cube.keys())) - 1
	hix = max(map(itemgetter(0), cube.keys())) + 2
	hiy = max(map(itemgetter(1), cube.keys())) + 2
	hiz = max(map(itemgetter(2), cube.keys())) + 2
	hiw = max(map(itemgetter(3), cube.keys())) + 2

	for x, y, z, w in product(range(lox, hix), range(loy, hiy), range(loz, hiz), range(low, hiw)):
		cell = cube[x, y, z, w]
		alive = neigh4d(cube, x, y, z, w)

		if cell == '#':
			if alive not in (2, 3):
				new[x, y, z, w] = '.'
		elif cell == '.':
			if alive == 3:
				new[x, y, z, w] = '#'

	return new

cube = defaultdict(lambda: '.')

for x, row in enumerate(startgrid):
	for y, cell in enumerate(row):
		cube[x, y, 0, 0] = cell


for _ in range(6):
	cube = evolve4d(cube)


ans2 = sum(x == '#' for x in cube.values())
advent.print_answer(2, ans2)
