#!/usr/bin/env python3

import os
import sys
import pickle
from subprocess import call
from multiprocessing import Pool
from PIL import Image, ImageFont, ImageDraw

def gen_frame(n):
	sys.stderr.write('Generating frame #{}...\r'.format(n))
	sys.stderr.flush()

	fontsize = 16
	fontw = fontsize - 7 # dat fine tuning right there

	with open('grids/grid_{:03d}.pkl'.format(n), 'rb') as f:
		data = pickle.load(f)

	grid    = data['grid']
	carts   = data['carts']
	crashed = data['crashed']

	h, w = len(grid), len(grid[0])
	h, w = h*fontsize, w*fontw

	font = ImageFont.truetype('consolas.ttf', fontsize)

	im   = Image.open(open('_pngs/frame_{:03d}.png'.format(n), 'rb'), mode='r')
	draw = ImageDraw.Draw(im)

	for i, line in enumerate(grid, 1):
		draw.text((0, i*fontsize), ''.join(line), font=font, fill=(64, 64, 64))

	for i, j in crashed:
		draw.text((j*fontw, (i+1)*fontsize), 'X', font=font, fill=(255, 0, 0))

	for i, j, d, _ in carts:
		draw.text((j*fontw, (i+1)*fontsize), d, font=font, fill=(255, 255, 255))

	im.save('pngs/frame_{:03d}.png'.format(n))

###########################################################

UP       = '^'
DOWN     = 'v'
RIGHT    = '>'
LEFT     = '<'

DIRECTIONS = (UP, DOWN, RIGHT, LEFT)
crashed = set()

if not os.path.isdir('grids') or len(os.listdir('grids')) == 0:
	sys.stderr.write('First generate the grids running generate_grids.py script!\n')
	sys.exit(1)

if not all(f.endswith('.pkl') for f in os.listdir('grids')):
	sys.stderr.write('Unrecognized file in the ./grids/ folder, clean it and regenerate the files!\n')
	sys.stderr.write('Make sure all file names are in the format grid_XXX.pkl\n')
	sys.exit(1)

if not os.path.isdir('pngs'):
	os.mkdir('pngs')

nthreads = 8
nframes = len(os.listdir('grids'))

sys.stderr.write('Starting {} threads to generate {} frames.\n'.format(nthreads, nframes))
sys.stderr.write('This... might take some time... sit back and relax!\n')
threadpool = Pool(nthreads)

threadpool.map(gen_frame, range(nframes))

sys.stderr.write('\nDone! All {} fames generated.        \n'.format(nframes))
sys.stderr.write('Now launching ffmpeg...\n')

videoname = 'animation.mp4'
call(['ffmpeg', '-i', 'pngs/frame_%03d.png', '-vf', 'transpose=2', '-vframes', str(nframes), videoname])

sys.stderr.write('Done! Created {}\n'.format(videoname))
