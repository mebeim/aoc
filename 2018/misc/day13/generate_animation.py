#!/usr/bin/env python3

import os
import sys
import pickle
from subprocess import call
from multiprocessing import Pool
from PIL import Image, ImageFont, ImageDraw

def gen_base_frame(base_grid):
	h, w = len(base_grid), len(base_grid[0])
	h, w = h*FONTSIZE, w*FONTW

	im   = Image.new('RGB', (w, h))
	draw = ImageDraw.Draw(im)

	for i, line in enumerate(base_grid):
		draw.text((0, i*FONTSIZE), ''.join(line), font=FONT, fill=(64, 64, 64))

	return im

def get_data():
	with open(BASE_GRID_FNAME, 'rb') as f:
		base_grid = pickle.load(f)

	with open(DIFFS_FNAME, 'rb') as f:
		diffs = pickle.load(f)

	return gen_base_frame(base_grid), diffs

def gen_frame(n):
	sys.stderr.write('Generating frame #{}...\r'.format(n))
	sys.stderr.flush()

	carts, crashed = diffs[n]['carts'], diffs[n]['crashed']

	im   = base_frame.copy()
	draw = ImageDraw.Draw(im)

	for i, j in crashed:
		draw.text((j*FONTW, i*FONTSIZE), 'X', font=FONT, fill=(255, 0, 0))

	for i, j, d, _ in carts:
		draw.text((j*FONTW, i*FONTSIZE), d, font=FONT, fill=(255, 255, 255))

	im.save('frames/frame_{:04d}.png'.format(n))

###########################################################

UP       = '^'
DOWN     = 'v'
RIGHT    = '>'
LEFT     = '<'

DIRECTIONS       = (UP, DOWN, RIGHT, LEFT)
BASE_GRID_FNAME  = 'data/base_grid.pkl'
DIFFS_FNAME      = 'data/diffs.pkl'
FONTSIZE         = 16           # Careful here LOL
FONTW            = FONTSIZE - 7 # dat fine tuning right there
FONT             = ImageFont.truetype('consolas.ttf', FONTSIZE)
VIDEO_FNAME      = 'animation.mp4'

if not os.path.isfile(BASE_GRID_FNAME) or not os.path.isfile(DIFFS_FNAME):
	sys.stderr.write('Missing required data. Generate it running ./generate_data.py first!\n')
	sys.exit(1)

if not os.path.isdir('frames'):
	os.mkdir('frames')

sys.stderr.write('Getting data and generating base frame... ')

base_frame, diffs = get_data()

sys.stderr.write('done.\n')

nthreads    = 8
nframes     = len(diffs)
crashed     = set()
ffmpeg_args = ['ffmpeg', '-i', 'frames/frame_%04d.png', '-vf', 'transpose=2', '-vframes', str(nframes), VIDEO_FNAME]

sys.stderr.write('Starting {} threads to generate {} frames.\n'.format(nthreads, nframes))

threadpool = Pool(nthreads)
threadpool.map(gen_frame, range(nframes))

sys.stderr.write('Done! All {} frames generated.          \n'.format(nframes))
sys.stderr.write('Now launching ffmpeg...\n')
sys.stderr.write(' '.join(ffmpeg_args) + '\n')

call(ffmpeg_args)

sys.stderr.write('Done! Created {}\n'.format(VIDEO_FNAME))
