#!/usr/bin/env python3

from utils import advent

advent.setup(2018, 11)
fin = advent.get_input()

##################################################

def fuel(x, y):
	rid = x + 10
	powlevel = ((((rid*y + serial_no)*rid) // 100) % 10) - 5
	return powlevel

def get_power(xy, m=3):
	s = 0
	x, y = xy
	for j in range(y, y+m):
		for i in range(x, x+m):
			s += grid[j][i]
	return s

serial_no = int(fin.read())

grid = []
for j in range(300+1):
	grid.append([])
	for i in range(300+1):
		grid[j].append(fuel(i, j))

# serial_no = 18
# for l in grid[45:45+3]:
# 	print(l[33:33+3])

ans = max(((x, y) for x in range(1, 301-3+1) for y in range(1, 301-3+1)), key=get_power)
advent.submit_answer(1, '{},{}'.format(*ans))

maxp = get_power(ans)
maxpsize = 2
print('to beat:', maxp)

prevp = maxp
consecutive_desc = 0

for sz in range(1, 301):
	print('size', sz, '...', end=' ')
	ans = max(((x, y) for x in range(1, 301-sz+1) for y in range(1, 301-sz+1)), key=lambda xy: get_power(xy, sz))
	p = get_power(ans, sz)
	print(ans, p)

	if p > maxp:
		maxp = p
		maxpsize = sz
		maxans = ans
		print('------------------------> new max')

	if p < prevp:
		consecutive_desc += 1
	else:
		consecutive_desc = 0

	# this is totally arbitrary... lol
	if consecutive_desc >= 5:
		break

	prevp = p

advent.submit_answer(2, '{},{},{}'.format(*maxans, maxpsize))

# #
# # Plot the grid for fun:
# #

# from PIL import Image
# im = Image.new('RGB', (300, 300))
# px = im.load()
# m = min(grid[i][j] for i in range(1, 301) for j in range(1, 301))
# M = max(grid[i][j] for i in range(1, 301) for j in range(1, 301))

# # Hardcoded values because I'm lazy as hell...
# # 231,107,14 p2
# # 233,36,3 p1

# for j in range(1, 301):
# 	for i in range(1, 301):
# 		if grid[j][i] < 0:
# 			v = int(grid[j][i]/m * 255)
# 			if i in range(231, 231+14+1) and j in range(107, 107+14+1):
# 				px[j-1, i-1] = (0, 128, v)
# 			elif i in range(233, 233+3+1) and j in range(36, 36+3+1):
# 				px[j-1, i-1] = (0, 128, v)
# 			else:
# 				px[j-1, i-1] = (0, 0, v)
# 		else:
# 			v = int(grid[j][i]/M * 255)
# 			if i in range(231, 231+14+1) and j in range(231, 107+14+1):
# 				px[j-1, i-1] = (v, 128, 0)
# 			elif i in range(233, 233+3+1) and j in range(36, 36+3+1):
# 				px[j-1, i-1] = (v, 128, 0)
# 			else:
# 				px[j-1, i-1] = (v, 0, 0)

# im = im.resize((300*8, 300*8))
# im.save('day11_visualized.png')
