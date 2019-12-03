#!/usr/bin/env python3

import advent
from collections import defaultdict

def make_move(s):
	return s[0], int(s[1:])

def get_visited(moves):
	dx = {'U': 0, 'D':  0, 'R': 1, 'L': -1}
	dy = {'U': 1, 'D': -1, 'R': 0, 'L':  0}
	visited = set()
	pathlen = defaultdict(lambda: float('inf'))
	cur_pathlen = 0
	p = (0, 0)

	for d, n in moves:
		for _ in range(n):
			p = (p[0] + dx[d], p[1] + dy[d])
			cur_pathlen += 1
			pathlen[p] = min(pathlen[p], cur_pathlen)
			visited.add(p)

	return visited, pathlen

def manhattan(ax, ay, bx, by):
	return abs(ax - bx) + abs(ay - by)


advent.setup(2019, 3, dry_run=True)
lines = advent.get_input().readlines()

all_visited = []
all_pathlen = []

for l in lines:
	visited, pathlen = get_visited(map(make_move, l.split(',')))
	all_visited.append(visited)
	all_pathlen.append(pathlen)

intersections = set.intersection(*all_visited)
min_distance = min(manhattan(*p, 0, 0) for p in intersections)

assert min_distance == 3247
advent.submit_answer(1, min_distance)

shortest_path = min(sum(l[p] for l in all_pathlen) for p in intersections)

assert shortest_path == 48054
advent.submit_answer(2, shortest_path)
