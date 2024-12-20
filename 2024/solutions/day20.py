#!/usr/bin/env python3

import sys
from collections import deque


def parse_grid(fin):
	walls  = set()
	spaces = set()

	for r, row in enumerate(map(str.rstrip, fin)):
		for c, char in enumerate(row):
			pos = r, c

			if char == '#':
				walls.add(pos)
			elif char in '.SE':
				spaces.add(pos)

				if char == 'S':
					start = pos
				elif char == 'E':
					end = pos

	return spaces, walls, start, end


def neighbors(r, c):
	for dr, dc in ((-1, 0), (1, 0), (0, -1), (0, 1)):
		yield r + dr, c + dc


def bfs_distances(spaces, walls, start):
	q = deque([start])
	dist = {start: 0}

	while q:
		p = q.popleft()

		for n in neighbors(*p):
			if n in dist or n in walls:
				continue

			dist[n] = dist[p] + 1
			q.append(n)

	return dist


def points_within_distance(r, c, maxdist):
	# Start from 2 to avoid the point itself and also to skip "useless" cheats
	# of only one cell (need at least 2 to pass through a wall of width 1)
	for dist in range(2, maxdist + 1):
		for d in range(dist):
			dd = dist - d
			yield (r + dd, c + d), dist
			yield (r - dd, c - d), dist
			yield (r + d, c - dd), dist
			yield (r - d, c + dd), dist


def count_good_cheats(dist_from_start, dist_from_end, target_dist, max_cheat_len=2):
	res = 0

	for pos, base_dist in dist_from_start.items():
		for cheat_end, cheat_dist in points_within_distance(*pos, max_cheat_len):
			if cheat_end not in dist_from_end:
				continue

			dist = base_dist + cheat_dist + dist_from_end[cheat_end]
			res += dist <= target_dist

	return res


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

spaces, walls, start, end = parse_grid(fin)

dist_from_start = bfs_distances(spaces, walls, start)
dist_from_end   = bfs_distances(spaces, walls, end)
target_dist     = dist_from_start[end] - 100

total1 = count_good_cheats(dist_from_start, dist_from_end, target_dist)
print('Part 1:', total1)

total2 = count_good_cheats(dist_from_start, dist_from_end, target_dist, 20)
print('Part 2:', total2)
