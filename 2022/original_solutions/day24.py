#!/usr/bin/env python3

from utils.all import *

def move_blizzard(bliz):
	newbliz = defaultdict(list)

	for (r, c), dirs in bliz.items():
		for dr, dc in dirs:
			newbliz[(r + dr) % HEIGHT, (c + dc) % WIDTH].append((dr, dc))

	return newbliz

def neighbors(bliz, r, c):
	if r == MAXR and c == MAXC:
		yield MAXR + 1, MAXC

	if r == 0 and c == 0:
		yield (-1, 0)

	for dr, dc in ((0, 1), (1, 0), (0, -1), (-1, 0)):
		rr, cc = r + dr, c + dc
		if 0 <= rr <= MAXR and 0 <= cc <= MAXC and (rr, cc) not in bliz:
			yield rr, cc

	if (r, c) not in bliz:
		yield r, c

def search(bliz, src, dst):
	positions = {src}
	time = 0

	while 1:
		prev_bliz = bliz
		bliz = move_blizzard(bliz)
		new_positions = set()

		for pos in positions:
			if pos == dst:
				return time, prev_bliz

			new_positions.update(neighbors(bliz, *pos))

		time += 1
		positions = new_positions

	raise RuntimeError('wtf no path?')

def dump(bliz, me=None):
	mp = {
		(0, 1) : '>',
		(0, -1): '<',
		(1, 0) : 'v',
		(-1, 0): '^',
	}

	res = ''
	for r in range(MAXR + 1):
		for c in range(MAXC + 1):
			if (r, c) == me:
				res += 'E'
			elif (r, c) in bliz:
				x = bliz[r, c]
				if len(x) > 1:
					res += str(len(x))
				else:
					res += mp[x[0]]
			else:
				res += '.'

		res += '\n'

	eprint(res)


advent.setup(2022, 24)
DEBUG = 'debug' in map(str.lower, sys.argv)
fin = advent.get_input() if not DEBUG else io.StringIO('''\
#.######
#>>.<^<#
#.<..<<#
#>v.><>#
#<^v^^>#
######.#
''')

grid = read_char_matrix(fin)
timer_start()

g = []
for row in grid[1:-1]:
	g.append(row[1:-1])
grid = g

# dump_char_matrix(grid)

HEIGHT, WIDTH = len(grid), len(grid[0])
MAXR, MAXC = HEIGHT - 1, WIDTH - 1
src = (-1, 0)
dst = (MAXR + 1, MAXC)

bliz = defaultdict(list)

for r, row in enumerate(grid):
	for c, cell in enumerate(row):
		if cell == '>':
			bliz[r,c].append((0, 1))
		elif cell == '<':
			bliz[r,c].append((0, -1))
		elif cell == 'v':
			bliz[r,c].append((1, 0))
		elif cell == '^':
			bliz[r,c].append((-1, 0))


ans, bliz = search(bliz, src, dst)

# 266 wrong
# 265 wrong
# 239 wrong
# 228 wrong
assert ans not in (266, 265, 239, 228), f'bad answer ffs: {ans}'
advent.print_answer(1, ans)


x, bliz = search(bliz, dst, src)
y, bliz = search(bliz, src, dst)
ans += x + y

advent.print_answer(2, ans)
