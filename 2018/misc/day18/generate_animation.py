#!/usr/bin/env python3

import os
import sys
import copy
import pickle
from subprocess import call
from multiprocessing import Pool
from collections import namedtuple
from random import choice as randchoice
from PIL import Image, ImageDraw

def iter_diagonals(sz, matrix=None):
	for diag_len in range(sz+1):
		for i, j in zip(range(diag_len-1, -1, -1), range(diag_len)):
			yield diag_len, diag_len-1, j, matrix[i][j] if matrix else None

	for diag_len in range(sz-1, 0, -1):
		for i, j in zip(range(sz-1, sz-diag_len-1, -1), range(sz-diag_len, sz)):
			yield diag_len, 2*sz-diag_len-1, sz-j-1, matrix[i][j] if matrix else None

def get_grid_size():
	with open('data/grid_{:04d}.pkl'.format(0), 'rb') as f:
		grid = pickle.load(f)

	sz = len(grid)
	assert len(grid[0]) == sz

	return sz

def gen_base_frame():
	w = CELL_WIDTH*grid_size + 2*PAD_HORIZONTAL
	h = CELL_HEIGHT*grid_size + 2*PAD_VERTICAL

	im = Image.new('RGB', (w, h))
	ImageDraw.Draw(im).rectangle([(0, 0), (w, h)], fill=(255, 255, 255))

	for i in range(-grid_size, 3*grid_size): # who gives a fuck
		for j in range(-grid_size, grid_size):
			x = w//2 + CELL_WIDTH*j + (CELL_WIDTH//2)*(i%2) - BG_TILE_OUT.cx
			y = PAD_VERTICAL + (CELL_HEIGHT//2)*(i+1) - BG_TILE_OUT.cy

			im.paste(BG_TILE_OUT.img, (x, y), BG_TILE_OUT.img)

	for diaglen, i, j, _ in iter_diagonals(grid_size):
		x = w//2 + CELL_WIDTH*(j - diaglen//2) + (CELL_WIDTH//2)*(i%2) - BG_TILE_IN.cx
		y = PAD_VERTICAL + (CELL_HEIGHT//2)*(i+1) - BG_TILE_IN.cy

		im.paste(BG_TILE_IN.img, (x, y), BG_TILE_IN.img)

	return im, w, h

def gen_frame(n):
	sys.stderr.write('Generating frame #{:d}...     \r'.format(n))
	sys.stderr.flush()

	with open('data/grid_{:04d}.pkl'.format(n), 'rb') as f:
		grid = pickle.load(f)
		assert len(grid) == len(grid[0]) == grid_size

	im = base_frame.copy()

	for diaglen, i, j, cell in iter_diagonals(grid_size, grid):
		tiles = TILES.get(cell)

		if tiles:
			tile = randchoice(tiles)
			x = frame_width//2 + CELL_WIDTH*(j - diaglen//2) + (CELL_WIDTH//2)*(i%2) - tile.cx
			y = PAD_VERTICAL + (CELL_HEIGHT//2)*(i+1) - tile.cy

			im.paste(tile.img, (x, y), tile.img)

	im.save('frames/frame_{:04d}.png'.format(n))


Tile = namedtuple('Tile', ['img', 'cx', 'cy'])

EMPTY, TREE, LUMB = range(3)

# Tweak below...

CELL_WIDTH     = 80
CELL_HEIGHT    = 40
PAD_HORIZONTAL = 20
PAD_VERTICAL   = 80

BG_TILE_OUT = Tile(
	Image.open('tiles/snow.png').resize((CELL_WIDTH, CELL_HEIGHT)),
	CELL_WIDTH//2,
	CELL_HEIGHT//2
)

BG_TILE_IN = Tile(
	Image.open('tiles/snow_field.png').resize((CELL_WIDTH, CELL_HEIGHT)),
	CELL_WIDTH//2,
	CELL_HEIGHT//2
)

TILES = {
	TREE: [
		Tile(Image.open('tiles/pine{}.png'.format(i)), 30, 77)
		for i in (1, 2, 3, 4, 5)
	],
	LUMB: [
		Tile(Image.open('tiles/lumb{}.png'.format(i)), 26, 28)
		for i in (1, 2, 3)
	] + [
		Tile(Image.open('tiles/lumb{}.png'.format(i)), 26, 34)
		for i in (4, 5)
	] + [
		Tile(Image.open('tiles/lumb6.png'), 26, 44)
	]
}

# NTHREADS    = 8
VIDEO_FNAME = 'animation.mp4'


if not os.path.isdir('data'):
	sys.stderr.write('Missing required data. Generate it running ./generate_data.py first!\n')
	sys.exit(1)

if not os.path.isdir('frames'):
	os.mkdir('frames')

sys.stderr.write('Generating background...')
sys.stderr.flush()

grid_size = get_grid_size()
base_frame, frame_width, frame_height = gen_base_frame()

sys.stderr.write('done.\n')

grid_fnames = os.listdir('data')
nframes     = len(grid_fnames)
ffmpeg_args = ['ffmpeg', '-i', 'frames/frame_%04d.png', '-vframes', str(nframes), VIDEO_FNAME]

# sys.stderr.write('Starting {} threads to generate {} frames.\n'.format(NTHREADS, nframes))

# threadpool = Pool(NTHREADS)
# threadpool.map(gen_frame, range(nframes))

# For some reason generating frames using multiple threads makes PIL raise
# strange errors like "OSError: image file is truncated" :/ ugh.

sys.stderr.write('Generating {} frames.\n'.format(nframes))

for i in range(nframes):
	gen_frame(i)

sys.stderr.write('Done! All {} frames generated.          \n'.format(nframes))

sys.stderr.write('Now launching ffmpeg...\n')
sys.stderr.write(' '.join(ffmpeg_args) + '\n')

call(ffmpeg_args)

sys.stderr.write('Done! Created {}\n'.format(VIDEO_FNAME))
