#!/usr/bin/env python3

from utils import advent
from collections import defaultdict
from operator import itemgetter
from itertools import combinations
from math import prod # Python >= 3.8

def parse_input(fin):
	raw_tiles = fin.read().rstrip().split('\n\n')
	raw_tiles = map(str.splitlines, raw_tiles)
	tiles = {}

	for t in raw_tiles:
		tid = int(t[0][5:-1])
		tiles[tid] = t[1:]

	return tiles

def edge(matrix, side):
	if side == 'n':
		return matrix[0]
	if side == 's':
		return matrix[-1]
	if side == 'e':
		return ''.join(map(itemgetter(-1), matrix))
	# 'w'
	return ''.join(map(itemgetter(0), matrix))

def match_tiles(tiles):
	matching_sides = defaultdict(str)
	corners = {}

	for id_a, id_b in combinations(tiles, 2):
		a, b = tiles[id_a], tiles[id_b]

		for side_a in 'nsew':
			for side_b in 'nsew':
				edge_a, edge_b = edge(a, side_a), edge(b, side_b)

				if edge_a == edge_b or edge_a == edge_b[::-1]:
					matching_sides[id_a] += side_a
					matching_sides[id_b] += side_b

	for tid, sides in matching_sides.items():
		if len(sides) == 2:
			corners[tid] = sides

	assert len(corners) == 4
	return corners

def rotate90(matrix):
	return tuple(''.join(column)[::-1] for column in zip(*matrix))

def orientations(matrix):
	yield matrix
	for _ in range(3):
		matrix = rotate90(matrix)
		yield matrix

def arrangements(matrix):
	yield from orientations(matrix)
	yield from orientations(matrix[::-1])

def strip_edges(matrix):
	return [row[1:-1] for row in matrix[1:-1]]

def matching_tile(tile, tiles, side_a, side_b):
	edge_a = edge(tile, side_a)

	for other_id, other in tiles.items():
		if tile is other:
			continue

		for other in arrangements(other):
			if edge_a == edge(other, side_b):
				tiles.pop(other_id)
				return other

def matching_row(prev, tiles, tiles_per_row):
	yield prev
	for _ in range(tiles_per_row - 1):
		tile = matching_tile(prev, tiles, 'e', 'w')
		prev = tile
		yield prev

def build_image(top_left_tile, tiles, image_dimension):
	first = top_left_tile
	image = []

	while 1:
		image_row = matching_row(first, tiles, image_dimension)
		image_row = map(strip_edges, image_row)
		image.extend(map(''.join, zip(*image_row)))

		if not tiles:
			break

		first = matching_tile(first, tiles, 's', 'n')

	return image

def count_pattern(image, pattern):
	pattern_h, pattern_w = len(pattern), len(pattern[0])
	image_sz = len(image)
	deltas = []

	for r, row in enumerate(pattern):
		for c, cell in enumerate(row):
			if cell == '#':
				deltas.append((r, c))

	for img in arrangements(image):
		n = 0
		for r in range(image_sz - pattern_h):
			for c in range(image_sz - pattern_w):
				if all(img[r + dr][c + dc] == '#' for dr, dc in deltas):
					n += 1

		if n != 0:
			return n

MONSTER_PATTERN = (
	'                  # ',
	'#    ##    ##    ###',
	' #  #  #  #  #  #   '
)


advent.setup(2020, 20)
fin = advent.get_input()

tiles   = parse_input(fin)
corners = match_tiles(tiles)
ans     = prod(corners)

advent.print_answer(1, ans)


top_left_id, matching_sides = corners.popitem()
top_left = tiles[top_left_id]

if matching_sides in ('ne', 'en'):
	top_left = rotate90(top_left)
elif matching_sides in ('nw', 'wn'):
	top_left = rotate90(rotate90(top_left))
elif matching_sides in ('sw', 'ws'):
	top_left = rotate90(rotate90(rotate90(top_left)))

image_dimension = int(len(tiles) ** 0.5)
tiles.pop(top_left_id)

image         = build_image(top_left, tiles, image_dimension)
monster_cells = sum(row.count('#') for row in MONSTER_PATTERN)
water_cells   = sum(row.count('#') for row in image)
n_monsters    = count_pattern(image, MONSTER_PATTERN)
roughness     = water_cells - n_monsters * monster_cells

advent.print_answer(2, roughness)
