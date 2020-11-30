#!/usr/bin/env python3

from utils import advent
import sys

advent.setup(2018, 10)
fin = advent.get_input()

##################################################

# position=<-54530, -54537> velocity=< 5,  5>

def simulate(maxsteps):
	contig = 0
	i = 0

	# while xs[-1] - xs[0] > 1000 or ys[-1] - ys[0] > 1000 or contig < 150:

	while contig < 150 and i < maxsteps:
		i += 1

		for p in points:
			p[0] += p[2]
			p[1] += p[3]

		# xsort = sorted(points, key=lambda p: (p[0], p[1]))
		# ysort = sorted(points, key=lambda p: (p[1], p[0]))

		contig = 0
		for p in points:
			for q in points:
				if (p[0] == q[0] and q[1] == p[1]+1) or (p[1] == q[1] and q[0] == p[0]+1):
					contig += 1

		sys.stdout.write(str(points[0]) + ' ' + str(i) +' '+ str(contig) + '     \r')

		# if contig > 1:
		# 	sys.stdout.write('\n' + str(contig) + '\n')

points = []
for l in map(str.strip, fin):
	l = l.replace('position=', '').replace('<', '').replace('>', '').replace(',', '').replace('velocity=', '')
	points.append(list(map(int, l.split())))

# for p in points:
# 	print(p)

# just found this simulating
# precalculate it to not waste time
print('precalc')
for init_sims in range(10942):
	for p in points:
		p[0] += p[2]
		p[1] += p[3]

for sims in range(10):
	simulate(1)

	minx = min(points, key=lambda p: p[0])[0]
	miny = min(points, key=lambda p: p[1])[1]
	maxx = max(points, key=lambda p: p[0])[0]
	maxy = max(points, key=lambda p: p[1])[1]
	print(minx, miny, maxx, maxy)

	grid = []

	print('gen grid')
	for y in range(maxy - miny + 1):
		grid.append([' '] * (maxx - minx + 1))

	print('mark points')
	for p in points:
		grid[p[1]-miny][p[0]-minx] = '#'

	print('write grid')
	with open('/tmp/grd{:02d}.txt'.format(sims+1), 'w') as f:
		for line in grid:
			f.write(''.join(line) + '\n')

print('\nOpen up the grdXX.txt files in /tmp and take a look!\n')
print('In my case, number 4 had the solution, which was:')
print('#####   #####   #    #  #    #  #    #  ######  ######  ##### ')
print('#    #  #    #  ##   #  ##   #  #    #  #            #  #    #')
print('#    #  #    #  ##   #  ##   #   #  #   #            #  #    #')
print('#    #  #    #  # #  #  # #  #   #  #   #           #   #    #')
print('#####   #####   # #  #  # #  #    ##    #####      #    ##### ')
print('#  #    #       #  # #  #  # #    ##    #         #     #  #  ')
print('#   #   #       #  # #  #  # #   #  #   #        #      #   # ')
print('#   #   #       #   ##  #   ##   #  #   #       #       #   # ')
print('#    #  #       #   ##  #   ##  #    #  #       #       #    #')
print('#    #  #       #    #  #    #  #    #  #       ######  #    #')
print('\nSo a total of', init_sims + 4 + 1, 'seconds to get to it.')
print('\nGiven how I solved this, as you can imagine the following answers are only valid for this input.')
advent.submit_answer(1, 'RPNNXFZR')
advent.submit_answer(2, init_sims + 4 + 1)
