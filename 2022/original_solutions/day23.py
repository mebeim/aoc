#!/usr/bin/env python3

from utils.all import *

MOVES = deque([
	((-1, 0), (-1, 1), (-1, -1), (-1, 0)),
	((1, 0), (1, 1), (1, -1), (1, 0)),
	((0, -1), (-1, -1), (1, -1), (0, -1)),
	((0, 1), (-1, 1), (1, 1), (0, 1)),
])

def move(grid, r, c):
	for dr,dc in ((-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)):
		if (r + dr, c + dc) in grid:
			break
	else:
		return

	for *deltas, want in MOVES:
		good = True
		for dr, dc in deltas:
			rr, cc = r + dr, c + dc
			if (rr, cc) in grid:
				good = False
				break

		dr, dc = want
		if good:
			rr, cc = r + dr, c + dc
			return rr, cc

def sim(grid):
	newg = set()
	nextpos = {}
	propcount = defaultdict(int)

	for r, c in grid:
		dst = move(grid, r, c)
		if dst is None:
			nextpos[r, c] = (r, c)
		else:
			propcount[dst] += 1
			nextpos[r, c] = dst

	for pos, newpos in nextpos.items():
		if propcount[newpos] == 1:
			r, c = newpos
			newg.add((r, c))
		else:
			r, c = pos
			newg.add((r, c))

	MOVES.rotate(-1)
	return newg

def dump(grid):
	rmin, rmax = min(map(itemgetter(0), grid)), max(map(itemgetter(0), grid))
	cmin, cmax = min(map(itemgetter(1), grid)), max(map(itemgetter(1), grid))
	res = ''

	for r in range(rmin, rmax+1):
		for c in range(cmin, cmax+1):
			if (r, c) not in grid:
				res += '.'
			else:
				res += '#'

		res += '\n'

	eprint(res)


advent.setup(2022, 23)
DEBUG = 'debug' in map(str.lower, sys.argv)
fin = advent.get_input() if not DEBUG else io.StringIO('''\
..............
..............
.......#......
.....###.#....
...#...#.#....
....#...##....
...#.###......
...##.#.##....
....#..#......
..............
..............
..............
''')

grid = read_char_matrix(fin)
timer_start()

actualgrid = set()
for r, row in enumerate(grid):
	for c, cell in enumerate(row):
		if cell == '#':
			actualgrid.add((r,c))

grid = actualgrid

# eprint('== Initial State ==')
# dump(grid)

for i in range(1, 10 + 1):
	grid = sim(grid)
	# eprint('\n== End of Round', i, '==')
	# dump(grid)

rmin, rmax = min(map(itemgetter(0), grid)), max(map(itemgetter(0), grid))
cmin, cmax = min(map(itemgetter(1), grid)), max(map(itemgetter(1), grid))

ans = 0
for r in range(rmin, rmax+1):
	for c in range(cmin, cmax+1):
		if (r, c) not in grid:
			ans += 1

# 4076 wrong
# 2512 wrong
advent.print_answer(1, ans)


for ans in count(11):
	old = grid
	grid = sim(grid)

	if grid == old:
		break

advent.print_answer(2, ans)
