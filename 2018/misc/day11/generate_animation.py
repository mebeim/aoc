#!/usr/bin/env python3

import os
import sys
import pickle
from PIL import Image
from subprocess import call

def gen_frame(serial_no, with_solutions, scale, offset=(0,0), crop_sz=(300, 300)):
	with open('grids/grid_{:03d}.pkl'.format(serial_no), 'rb') as f:
		data = pickle.load(f)

	grid = data['grid']
	p1x, p1y, p1sz = data['p1']
	p2x, p2y, p2sz = data['p2']

	iszx, iszy = offset
	szx, szy = crop_sz

	im = Image.new('RGB', (szx, szy))
	px = im.load()

	m = min(grid[i][j] for i in range(1, 301) for j in range(1, 301))
	M = max(grid[i][j] for i in range(1, 301) for j in range(1, 301))

	for j in range(iszy+1, szy+iszy+1):
		for i in range(iszx+1, szx+iszx+1):
			v   = int(grid[j][i]/(m, M)[grid[j][i] > 0] * 255)
			pos = (i-iszx-1, j-iszy-1)

			sol = with_solutions and (
				   (i in range(p1x, p1x+p1sz+1) and j in range(p1y, p1y+p1sz+1))
				or (i in range(p2x, p2x+p2sz+1) and j in range(p2y, p2y+p2sz+1))
			)

			if grid[j][i] < 0:
				px[pos] = (0, (0, 128)[sol], v)
			else:
				px[pos] = (v, (0, 128)[sol], 0)

	im = im.resize((szx*scale, szy*scale))
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

# Below settings render the full grid as a 2400x2400 pixels mp4 video if untouched.

start          = (0, 0)     # X,Y of starting point for frame generation.
size           = (300, 300) # Size of each frame (max 300x300 when start==(0,0)).
scale          = 8          # Scale factor of frames (1 grid cell = scale pixels).
draw_solutions = True       # Whether to include green squares representing the solutions on each frame.

for n in range(len(os.listdir('grids'))):
	sys.stderr.write('Generating frame #{}... '.format(n))
	sys.stderr.flush()

	gen_frame(n, draw_solutions, scale, start, size)

	sys.stderr.write('done.    \r')
	sys.stderr.flush()

sys.stderr.write('\nDone! Now launching ffmpeg...              \n')

videoname = 'animation_{}x{}_start{}-{}_scale{}_{}frames.mp4'.format(*size, *start, scale, n)
call(['ffmpeg', '-i', 'pngs/frame_%03d.png', '-vframes', str(n), videoname])

sys.stderr.write('Done! Created {}\n'.format(videoname))
