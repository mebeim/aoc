#!/usr/bin/env python3

from utils.all import *

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

lines = get_lines(fin)

def mktup(s):
	return s[0], int(s[1:])

def manhattan(ax, ay, bx, by):
	return abs(ax - bx) + abs(ay - by)

w1 = list(map(mktup, lines[0].split(',')))
w2 = list(map(mktup, lines[1].split(',')))

grid = defaultdict(int)

best1 = defaultdict(lambda: float('inf'))
p = (0, 0)
tot = 0

for d, n in w1:
	x, y = p

	if d == 'R':
		for dx in range(1, n+1):
			grid[x + dx, y] |= 1
			tot += 1
			best1[x + dx, y] = min(best1[x + dx, y], tot)
		p = x + n, y
	elif d == 'L':
		for dx in range(1, n+1):
			grid[x - dx, y] |= 1
			tot += 1
			best1[x - dx, y] = min(best1[x - dx, y], tot)
		p = x - n, y
	elif d == 'U':
		for dx in range(1, n+1):
			grid[x, y + dx] |= 1
			tot += 1
			best1[x, y + dx] = min(best1[x, y + dx], tot)
		p = x, y + n
	elif d == 'D':
		for dx in range(1, n+1):
			grid[x, y - dx] |= 1
			tot += 1
			best1[x, y - dx] = min(best1[x, y - dx], tot)
		p = x, y - n

best2 = defaultdict(lambda: float('inf'))
p = (0, 0)
tot = 0

for d, n in w2:
	x, y = p

	if d == 'R':
		for dx in range(1, n+1):
			grid[x + dx, y] |= 2
			tot += 1
			best2[x + dx, y] = min(best2[x + dx, y], tot)
		p = x + n, y
	elif d == 'L':
		for dx in range(1, n+1):
			grid[x - dx, y] |= 2
			tot += 1
			best2[x - dx, y] = min(best2[x - dx, y], tot)
		p = x - n, y
	elif d == 'U':
		for dx in range(1, n+1):
			grid[x, y + dx] |= 2
			tot += 1
			best2[x, y + dx] = min(best2[x, y + dx], tot)
		p = x, y + n
	elif d == 'D':
		for dx in range(1, n+1):
			grid[x, y - dx] |= 2
			tot += 1
			best2[x, y - dx] = min(best2[x, y - dx], tot)
		p = x, y - n

cross = [p for p in grid.keys() if grid[p] == 3]
ans = min(manhattan(*p, 0, 0) for p in cross)

advent.submit_answer(1, ans)

ans2 = float('inf')
for p in cross:
	if p in best1 and p in best2:
		ans2 = min(ans2, best1[p] + best2[p])

# print(ans2)
# 55554 not right
advent.submit_answer(2, ans2)
