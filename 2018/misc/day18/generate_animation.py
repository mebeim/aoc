#!/usr/bin/env python3

import os
import sys
import copy
import pickle
from subprocess import call
from multiprocessing import Pool
from PIL import Image

def get_grid_dimensions():
	with open('data/grid_{:04d}.pkl'.format(0), 'rb') as f:
		grid = pickle.load(f)

	return len(grid), len(grid[0])

def gen_base_frame():
	global frame_width
	global frame_height

	im = Image.new('RGB', (frame_width, frame_height))
	bg = Image.open('tiles/snow.png')

	tile_width, tile_height = bg.size

	for i in range(frame_width//tile_width + 1):
		for j in range(frame_height//tile_height + 1):
			im.paste(bg, (i*tile_width, j*tile_height))

	return im

def gen_frame(n):
	global frame_width
	global frame_height

	sys.stderr.write('Generating frames (#{:d})...     \r'.format(n))
	sys.stderr.flush()

	with open('data/grid_{:04d}.pkl'.format(n), 'rb') as f:
		grid = pickle.load(f)

	im = base_frame.copy()

	for i in range(gridw - 1, -1, -1):
		for j in range(gridh):
			cell = grid[j][i]

			x = PAD + i*(SZI+ISP) + SHIFT*j
			y = PAD + j*(SZJ+JSP)

			if cell != EMPTY:
				im.paste(SPRITEMAP[cell], (x, y), SPRITEMAP[cell])

	im.save('frames/frame_{:04d}.png'.format(n))

EMPTY, TREE, LUMB = range(3)

SPRITEMAP = [
	None,
	Image.open('tiles/tree.png').convert('RGBA'),
	Image.open('tiles/crates.png').convert('RGBA')
]

VIDEO_FNAME = 'animation.mp4'
NTHREADS    = 8

PAD   = 25
SHIFT = 30
ISP   = 0
JSP   = 15
SZI   = 48
SZJ   = SZI-SHIFT

if not os.path.isdir('data'):
	sys.stderr.write('Missing required data. Generate it running ./generate_data.py first!\n')
	sys.exit(1)

if not os.path.isdir('frames'):
	os.mkdir('frames')

gridw, gridh = get_grid_dimensions()
frame_width  = (gridw+1)*(SZI+ISP) + gridw*SHIFT + 2*PAD
frame_height = (gridh+1)*(SZJ+JSP) + 2*PAD
base_frame   = gen_base_frame()

grid_fnames = os.listdir('data')
nframes     = len(grid_fnames)
ffmpeg_args = ['ffmpeg', '-i', 'frames/frame_%04d.png', '-vframes', str(nframes), VIDEO_FNAME]

sys.stderr.write('Starting {} threads to generate {} frames.\n'.format(NTHREADS, nframes))

threadpool = Pool(NTHREADS)
threadpool.map(gen_frame, range(nframes))

sys.stderr.write('Done! All {} fames generated.          \n'.format(nframes))
sys.stderr.write('Now launching ffmpeg...\n')
sys.stderr.write(' '.join(ffmpeg_args) + '\n')

call(ffmpeg_args)

sys.stderr.write('Done! Created {}\n'.format(VIDEO_FNAME))
