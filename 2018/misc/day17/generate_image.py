#!/usr/bin/env python3

import sys
from PIL import Image, ImageDraw

SCALE = 8

COLOR_MAP = {
	' ': (234, 212, 157),
	'.': (234, 212, 157),
	'~': (30, 144, 255),
	'|': (102, 205, 170),
	'#': (138, 109, 38)
}

if len(sys.argv[1:]) != 1:
	sys.stderr.write('Usage {} input_ascii_art.txt\n'.format(sys.argv[0]))
	sys.exit(1)

grid = list(map(lambda l: l.rstrip('\n'), open(sys.argv[1])))

w, h = len(grid[0]), len(grid)

im = Image.new('RGB', (w * SCALE, h * SCALE))
dr = ImageDraw.Draw(im)

for i, row in enumerate(grid):
	for j, cell in enumerate(row):
		dr.rectangle([(j*SCALE, i*SCALE), ((j+1)*SCALE-1, (i+1)*SCALE-1)], fill=COLOR_MAP[cell])

im.save('day17_visualized.png')
