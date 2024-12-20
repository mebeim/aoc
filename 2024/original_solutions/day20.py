#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 20)
fin = advent.get_input()

grid = read_char_matrix(fin)

ans1 = ans2 = 0
HEIGHT, WIDTH = len(grid), len(grid[0])

def lr(r, c):
	cc = c - 1
	if 0 <= cc < WIDTH:
		yield r, cc

	cc = c + 1
	if 0 <= cc < WIDTH:
		yield r, cc

def ud(r, c):
	rr = r - 1
	if 0 <= rr < HEIGHT:
		yield rr, c

	rr = r + 1
	if 0 <= rr < HEIGHT:
		yield rr, c

def lrwall(r, c):
	n = 0
	for rr, cc in lr(r, c):
		n += grid[rr][cc] == '.'
	return n == 2

def udwall(r, c):
	n = 0
	for rr, cc in ud(r, c):
		n += grid[rr][cc] == '.'
	return n == 2


for r, row in enumerate(grid):
	for c, char in enumerate(row):
		if char == 'S':
			start = (r, c)
			grid[r][c] = '.'
		elif char == 'E':
			finish = (r, c)
			grid[r][c] = '.'


def neighbors_cheat(grid, r, c, avoid):
	if (r, c) == cheat1:
		for nr, nc in neighbors4(grid, r, c):
			if (nr, nc) == cheat2:
				yield nr, nc
	else:
		yield from neighbors4(grid, r, c, avoid)


cheat1 = (-10, -10)
cheat2 = (-10, -10)
initial = grid_bfs(grid, start, finish, avoid='#', get_neighbors=neighbors_cheat)
# eprint(initial)

# Slow as hell, but hey, gets the job done
for r, row in enumerate(grid):
	# eprint(r)
	for c, char in enumerate(row):
		if grid[r][c] == '#':
			if lrwall(r, c):
				cheat2 = r, c

				cheat1 = r, c - 1
				d = grid_bfs(grid, start, finish, avoid='#', get_neighbors=neighbors_cheat)
				saved = initial - d
				if saved >= 100:
					ans1 += 1

				cheat1 = r, c + 1
				d = grid_bfs(grid, start, finish, avoid='#', get_neighbors=neighbors_cheat)
				saved = initial - d
				if saved >= 100:
					ans1 += 1
			elif udwall(r, c):
				cheat2 = r, c

				cheat1 = r - 1, c
				d = grid_bfs(grid, start, finish, avoid='#', get_neighbors=neighbors_cheat)
				saved = initial - d
				if saved >= 100:
					ans1 += 1

				cheat1 = r + 1, c
				d = grid_bfs(grid, start, finish, avoid='#', get_neighbors=neighbors_cheat)
				saved = initial - d
				if saved >= 100:
					ans1 += 1

# 1416 wrong
advent.print_answer(1, ans1)



def distances(point):
	q = deque([point])
	dist = {point: 0}

	while q:
		p = q.popleft()

		for rr, cc in neighbors4(grid, *p, '#'):
			neigh = Vec(rr, cc)
			if neigh not in dist:
				dist[neigh] = dist[p] + 1
				q.append(neigh)

	return dist


def points_within_distance(p, maxdist):
	for dist in range(1, maxdist + 1):
		for d in range(dist):
			dd = dist - d
			yield p + (dd, d), dist
			yield p + (-dd, -d), dist
			yield p + (d, -dd), dist
			yield p + (-d, dd), dist


start = Vec(*start)
finish = Vec(*finish)
dist_from_start = distances(start)
dist_from_finish = distances(finish)

base = dist_from_start[finish]
x = defaultdict(int)

for r, row in enumerate(grid):
	for c, char in enumerate(row):
		if grid[r][c] == '#':
			continue

		cheat_start = Vec(r, c)
		for cheat_end, cheat_dist in points_within_distance(cheat_start, 20):
			if cheat_end not in dist_from_finish:
				continue

			dist = dist_from_start[cheat_start] + cheat_dist + dist_from_finish[cheat_end]
			saved = base - dist
			# x[saved] += 1

			if saved >= 100:
				ans2 += 1

# xx = sorted(x.items())
# for saved, count in xx:
# 	print(f'There are {count} cheats that save {saved} picoseconds.')

# 565805 wrong
advent.print_answer(2, ans2)
