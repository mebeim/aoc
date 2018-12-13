#!/usr/bin/env python3

import os
import sys
import pickle
from subprocess import call
from multiprocessing import Pool
from PIL import Image, ImageFont, ImageDraw

def gen_base_frame(data_fname):
	with open(data_fname, 'rb') as f:
		base_grid = pickle.load(f)

	h, w = len(base_grid), len(base_grid[0])
	h, w = h*FONTSIZE, w*FONTW

	im   = Image.new('RGB', (w, h))
	draw = ImageDraw.Draw(im)

	for i, line in enumerate(base_grid):
		draw.text((0, i*FONTSIZE), ''.join(line), font=FONT, fill=(64, 64, 64))

	return im

def gen_frame(n):
	sys.stderr.write('Generating frame #{}...\r'.format(n))
	sys.stderr.flush()

	with open('data/diff_{:04d}.pkl'.format(n), 'rb') as f:
		data = pickle.load(f)

	carts   = data['carts']
	crashed = data['crashed']

	im   = BASE_FRAME.copy()
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
BASE_GRID_FNAME  = 'data/base.pkl'
BASE_FRAME       = None
FONTSIZE         = 16           # Careful here LOL
FONTW            = FONTSIZE - 7 # dat fine tuning right there
FONT             = ImageFont.truetype('consolas.ttf', FONTSIZE)

if not os.path.isdir('data') or len(os.listdir('data')) == 0:
	sys.stderr.write('First generate the data running generate_data.py script!\n')
	sys.exit(1)

if not all(f.endswith('.pkl') for f in os.listdir('data')):
	sys.stderr.write('Unrecognized file in the ./data/ folder, clean it and regenerate the files!\n')
	sys.exit(1)

if not os.path.isdir('frames'):
	os.mkdir('frames')

nthreads = 8
nframes = len(os.listdir('data')) - 1
crashed = set()

sys.stderr.write('Generating base frame... ')

BASE_FRAME = gen_base_frame(BASE_GRID_FNAME)

sys.stderr.write('done.\n')

sys.stderr.write('Starting {} threads to generate {} frames.\n'.format(nthreads, nframes))
sys.stderr.write('This... might take some time... sit back and relax!\n')
threadpool = Pool(nthreads)

threadpool.map(gen_frame, range(nframes))

sys.stderr.write('\nDone! All {} fames generated.        \n'.format(nframes))
sys.stderr.write('Now launching ffmpeg...\n')

videoname = 'animation.mp4'
call(['ffmpeg', '-i', 'frames/frame_%04d.png', '-vf', 'transpose=2', '-vframes', str(nframes), videoname])

sys.stderr.write('Done! Created {}\n'.format(videoname))
