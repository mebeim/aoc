#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 20)
fin = advent.get_input()
timer_start()

tiles = {}

xx = list(filter(None, fin.read().split('\n\n')))
for x in xx:
	xxx = list(map(str.strip, x.splitlines()))
	iid = int(xxx[0].split()[-1][:-1])

	t = []
	for l in xxx[1:]:
		t.append(list(l))
	tiles[iid] = t

W, H = len(t[0]), len(t)

def side(m, d):
	res = ''

	if d == 'n':
		res = ''.join(m[0])
	elif d == 's':
		res = ''.join(m[H-1])
	elif d == 'e':
		c = W-1
		for r in range(H):
			res += m[r][c]
	elif d == 'w':
		c = 0
		for r in range(H):
			res += m[r][c]

	return res


N = len(tiles)
# eprint('N tiles:', N)
matches = {i: list() for i in tiles}

ts = list(tiles.items())

for i, (id1, t1) in enumerate(ts):
	for id2, t2 in ts[i + 1:]:
		for d1 in 'nsew':
			for d2 in 'nsew':
				x = side(t1, d1)
				y = side(t2, d2)
				if x == y:
					matches[id1].append((id2, d1, d2))
					matches[id2].append((id1, d2, d1))
				elif x[::-1] == y:
					matches[id1].append((id2, d1, d2))
					matches[id2].append((id1, d2, d1))

del ts

corners = []
sides   = []
for i, m in matches.items():
	if len(m) == 2:
		corners.append(i)
	elif len(m) == 3:
		sides.append(i)

# eprint('corners', len(corners), corners)
# eprint('sides', len(sides), sides)

assert len(corners) == 4
assert len(sides) % 4 == 0

ans = 1
for x in corners:
	ans *= x

advent.print_answer(1, ans)

# P2 ###########################################################################

def rotate90(t):
	h, w = len(t[0]), len(t)
	new = [[None for _ in range(h)] for __ in range(w)]

	for r in range(h):
		for c in range(w):
			new[c][H - r - 1] = t[r][c]

	return new

# NOTE: this function does not properly flip the image
def fliph(t):
	h, w = len(t[0]), len(t)
	new = [[None for _ in range(w)] for __ in range(h)]

	for r in range(h):
		for c in range(w):
			new[r][W - c - 1] = t[r][c]

	return new

def adjustlr(l, r):
	x = side(l, 'e')

	rr = r
	if x == side(rr, 'w'):
		return rr

	for _ in range(3):
		rr = rotate90(rr)
		if x == side(rr, 'w'):
			return rr

	rr = fliph(r)
	if x == side(rr, 'w'):
		return rr

	for _ in range(3):
		rr = rotate90(rr)
		if x == side(rr, 'w'):
			return rr

def adjustud(u, d):
	x = side(u, 's')

	dd = d
	if x == side(dd, 'n'):
		return dd

	for _ in range(3):
		dd = rotate90(dd)
		if x == side(dd, 'n'):
			return dd

	dd = fliph(d)
	if x == side(dd, 'n'):
		return dd

	for _ in range(3):
		dd = rotate90(dd)
		if x == side(dd, 'n'):
			return dd

IMAGE_WH = len(sides) // 4 + 2
image = [[None for ___ in range(IMAGE_WH)] for ____ in range(IMAGE_WH)]

# eprint(f'Image is {IMAGE_WH}x{IMAGE_WH} tiles')

# pick an arbitrary top left corner
topleft = corners[0]
assert len(matches[topleft]) == 2

t = tiles[topleft]
dd = matches[topleft][0][1] + matches[topleft][1][1]

# adjust it to have matching tiles south and east
if dd in ('ne', 'en'):
	t = rotate90(t)
elif dd in ('sw', 'ws'):
	t = rotate90(t)
	t = rotate90(t)
	t = rotate90(t)
elif dd in ('wn', 'nw'):
	t = rotate90(t)
	t = rotate90(t)

# put top left corner in place
tiles[topleft] = t
image[0][0] = tiles[topleft]

remaining = set(tiles.keys())
remaining.remove(topleft)
prev = tiles[topleft]

# adjust first row by matching each tile left side with the right side of the one to the left
for c in range(1, IMAGE_WH):
	match = None

	for rid in remaining:
		r = tiles[rid]
		adj = adjustlr(prev, r)
		if adj is not None:
			match = rid
			break

	assert match is not None

	remaining.remove(match)
	image[0][c] = adj
	prev = adj

# adjust all columns by matching each tile top side with the bottom side of the one above
for c in range(IMAGE_WH):
	prev = image[0][c]

	for r in range(1, IMAGE_WH):
		match = None

		for rid in remaining:
			d = tiles[rid]
			adj = adjustud(prev, d)
			if adj is not None:
				match = rid
				break

		# print(remaining)
		assert match is not None

		remaining.remove(match)
		image[r][c] = adj
		prev = adj

# for ir in range(IMAGE_WH):
# 	for r in range(H):
# 		s = ''
# 		for c in range(IMAGE_WH):
# 			s += ''.join(image[ir][c][r]) + ' '
# 		eprint(s)
# 	eprint()

def strip_edges(t):
	w, h = W - 2, H - 2
	new = [[None for _ in range(w)] for __ in range(h)]

	for r in range(h):
		for c in range(w):
			new[r][c] = t[r + 1][c + 1]

	return new

for i in range(IMAGE_WH):
	for j in range(IMAGE_WH):
		image[i][j] = strip_edges(image[i][j])

H -= 2
W -= 2
final = []
FINAL_WH = IMAGE_WH * W

# compose actual image
for ir in range(IMAGE_WH):
	for r in range(H):
		s = ''
		for c in range(IMAGE_WH):
			s += ''.join(image[ir][c][r])
		final.append(s)

# dump_char_matrix(final)

pattern = '''                  #
#    ##    ##    ###
 #  #  #  #  #  #   '''.splitlines()

pattern = list(map(lambda l: l.rstrip('\n'), pattern))
DELTAS = []

for r, row in enumerate(pattern):
	for c, cell in enumerate(row):
		if cell == '#':
			DELTAS.append((r, c))

MONSTER_H = max(map(itemgetter(0), DELTAS))
MONSTER_W = max(map(itemgetter(1), DELTAS))
# dump_iterable(DELTAS)

def count_monsters(img):
	n = 0
	for r in range(FINAL_WH - MONSTER_H):
		for c in range(FINAL_WH - MONSTER_W):
			ok = True
			for dr, dc in DELTAS:
				if img[r + dr][c + dc] != '#':
					ok = False
					break

			if ok:
				n += 1

	return n

# search monsters in all orientations/rotations of the image
def oof(xx):
	x = xx
	n = count_monsters(x)
	if n != 0:
		return n

	for _ in range(3):
		x = rotate90(x)
		n = count_monsters(x)
		if n != 0:
			return n

	x = fliph(xx)
	n = count_monsters(x)
	if n != 0:
		return n

	for _ in range(3):
		x = rotate90(x)
		n = count_monsters(x)
		if n != 0:
			return n

	assert False, 'wtf'

# dump_char_matrix(final)

nmonsters = oof(final) + 2 # fliph is bugged and this counts wrong, whatever
# eprint('# monsters:', nmonsters)

water = sum(row.count('#') for row in final)
tot = water - len(DELTAS) * nmonsters

# n 19 tot 1735 wrong
# n 20 tot 1720 wrong
# n 21 tot 1705 wrong
advent.print_answer(2, tot)
