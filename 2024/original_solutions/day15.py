#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 15)
DEBUG = 'debug' in map(str.lower, sys.argv)
fin = advent.get_input() if not DEBUG else io.StringIO('''\
##########
#..O..O.O#
#......O.#
#.OO..O.O#
#..O@..O.#
#O#..O...#
#O..O..O.#
#.OO.O.OO#
#....O...#
##########

<vv>^<v^>v>^vv^v>v<>v^v<v<^vv<<<^><<><>>v<vvv<>^v^>^<<<><<v<<<v^vv^v>^
vvv<<^>^v^^><<>>><>^<<><^vv^^<>vvv<>><^^v>^>vv<>v<<<<v<^v>^<^^>>>^<v<v
><>vv>v^v^<>><>>>><^^>vv>v<^^^>>v^v^<^^>v^^>v^<^v>v<>>v^v^<v>v^^<^^vv<
<<v<^>>^^^^>>>v^<>vvv^><v<<<>^^^vv^<vvv>^>v<^^^^v<>^>vvvv><>>v^<<^^^^^
^><^><>>><>^^<<^^v>>><^<v>^<vv>>v>>>^v><>^v><<<<v>>v<v<v>vvv>^<><<>^><
^>><>^v<><^vvv<^^<><v<<<<<><^v<<<><<<^^<v<^^^><^>>^<v^><<<^>>^v<v^v<v^
>^>>^v>vv>^<<^v<>><<><<v<<v><>v<^vv<<<>^^v^>^^>>><<^v>>v^v><^^>>^<>vv^
<><^^>^^^<><vvvvv^v<v<<>^v<v>v<<^><<><<><<<^^<<<^<<>><<><^^^>^^<>^>v<>
^^>vv<^v^v<vv>^<><v<^v>^^^>>>^^vvv^>vvv<>>>^<^>>>>>^<<^v>^vvv<>^<><<v>
v^^>>><<^^<>>^v^<v^vv<>v^<<>^<^v^v><^<<<><<^<v><v<>vv>>v><v^<vv<>v^<<^
''')

data = fin.read()
grid, moves = data.split('\n\n')
grid = read_char_matrix(io.StringIO(grid))
ans1 = ans2 = 0

movemap = {
	'^': Vec(-1, 0),
	'v': Vec(1, 0),
	'>': Vec(0, 1),
	'<': Vec(0, -1)
}

walls = set()
boxes = set()

for r, row in enumerate(grid):
	for c, cell in enumerate(row):
		if cell == '@':
			start = Vec(r, c)
		elif cell == '#':
			walls.add(Vec(r,c))
		elif cell == 'O':
			boxes.add(Vec(r,c))

p = start
for m in moves.strip():
	if m not in movemap:
		continue

	delta = movemap[m]

	newp = p + delta
	if newp in walls:
		continue

	if newp not in boxes:
		p = newp
		continue

	box = newp
	tomove = []
	while box in boxes:
		tomove.append(box)
		box += delta

	if box in walls:
		continue

	for box in tomove:
		boxes.discard(box)
	for box in tomove:
		boxes.add(box + delta)

	p = newp

for box in boxes:
	ans1 += 100 * box.r + box.c

advent.print_and_submit(1, ans1)


walls = set()
box_pieces = {}

for r, row in enumerate(grid):
	for c, cell in enumerate(row):
		if cell == '@':
			start = Vec(r, 2 * c)
		elif cell == '#':
			walls.add(Vec(r, 2 * c))
			walls.add(Vec(r, 2 * c + 1))
		elif cell == 'O':
			a, b = Vec(r, 2 * c), Vec(r, 2 * c + 1)
			box_pieces[a] = (a, b)
			box_pieces[b] = (a, b)


def adj_boxes(box, delta):
	a, b = box
	xa = box_pieces.get(a + delta)
	xb = box_pieces.get(b + delta)

	if delta != (0, -1):
		if xb is not None:
			yield xb

	if delta != (0, 1):
		if xa is not None:
			yield xa

def find_boxes(box, delta):
	q = deque([box])
	seen = set()

	while q:
		box = q.popleft()
		if box in seen:
			continue

		seen.add(box)
		if box[0] + delta in walls or box[1] + delta in walls:
			return None

		q.extendleft(adj_boxes(box, delta))

	return seen

def display(p):
	if not DEBUG:
		return

	dikt = {p: '@'}
	for w in walls:
		dikt[w] = '#'

	for a, b in box_pieces.values():
		dikt[a] = '['
		dikt[b] = ']'

	print('-' * 50)
	dump_sparse_matrix(dikt)


p = start
for m in moves.strip():
	if m not in movemap:
		continue

	display(p)
	delta = movemap[m]

	newp = p + delta
	if newp in walls:
		continue

	if newp not in box_pieces:
		p = newp
		continue

	box = box_pieces[newp]
	tomove = find_boxes(box, delta)
	if tomove is None:
		continue

	for box in tomove:
		a, b = box
		del box_pieces[a]
		del box_pieces[b]

	for box in tomove:
		a, b = box
		aa, bb = a + delta, b + delta
		box_pieces[aa] = (aa, bb)
		box_pieces[bb] = (aa, bb)

	p = newp

display(p)

for box in box_pieces.values():
	ans2 += 100 * box[0].r + box[0].c

ans2 //= 2

advent.print_answer(2, ans2)
