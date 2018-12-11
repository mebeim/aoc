#!/usr/bin/env python3

import os
import sys
import pickle
from PIL import Image
from subprocess import call

#
# Plot the grid for fun.
#

def gen_frame(serial_no, with_solutions, scale, crop_top=(300, 300)):
	with open('grids/grid_{:03d}.pkl'.format(serial_no), 'rb') as f:
		data = pickle.load(f)

	grid = data['grid']
	p1x, p1y, p1sz = data['p1']
	p2x, p2y, p2sz = data['p2']

	szx, szy = crop_top

	im = Image.new('RGB', (szy, szx))
	px = im.load()

	m = min(grid[i][j] for i in range(1, 301) for j in range(1, 301))
	M = max(grid[i][j] for i in range(1, 301) for j in range(1, 301))

	for j in range(1, szy+1):
		for i in range(1, szx+1):
			if grid[j][i] < 0:
				v = int(grid[j][i]/m * 255)

				if with_solutions and ((i in range(p1x, p1x+p1sz+1) and j in range(p1y, p1y+p1sz+1)) or (i in range(p2x, p2x+p2sz+1) and j in range(p2y, p2y+p2sz+1))):
					px[j-1, i-1] = (0, 128, v)
				else:
					px[j-1, i-1] = (0, 0, v)
			else:
				v = int(grid[j][i]/M * 255)

				if with_solutions and ((i in range(p1x, p1x+p1sz+1) and j in range(p1y, p1y+p1sz+1)) or (i in range(p2x, p2x+p2sz+1) and j in range(p2y, p2y+p2sz+1))):
					px[j-1, i-1] = (v, 128, 0)
				else:
					px[j-1, i-1] = (v, 0, 0)

	im = im.resize((szy*scale, szx*scale))
	im.save('pngs/frame_{:03d}.png'.format(serial_no))

#######################################################

if not os.path.isdir('grids') or len(os.listdir('grids')) == 0:
	sys.stderr.write('First generate the grids running generate_grids.py script!\n')
	sys.exit(1)

if not all(f.endswith('.pkl') for f in os.listdir('grids')):
	sys.stderr.write('Unrecognized file in the ./grids/ folder, clean it and regenerate the files!\n')
	sys.stderr.write('Make sure all file names are in the format grid_XXX.pkl\n')
	sys.exit(1)

if not os.path.isdir('pngs'):
	os.mkdir('pngs')

scale = 8
crop_top = (300, 300) # Inverted, height first! Max 300x300.

for n in range(len(os.listdir('grids'))):
	sys.stderr.write('Generating frame #{}... '.format(n))
	sys.stderr.flush()

	gen_frame(n, False, scale, crop_top)

	sys.stderr.write('done.    \r')
	sys.stderr.flush()

sys.stderr.write('Done! Now launching ffmpeg...              \n')

videoname = 'animation_{}x{}_scalex{}_{}frames.mp4'.format(*crop_top[::-1], scale, n)
call(['ffmpeg', '-i', 'pngs/frame_%03d.png', '-vframes', str(n), videoname])

sys.stderr.write('Done! Created {}\n'.format(videoname))
