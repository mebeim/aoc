#!/usr/bin/env python3

from collections import defaultdict
from string import ascii_lowercase

def make_move(s):
	return s[0], int(s[1:])

def get_visited(moves):
	lower = set(ascii_lowercase)
	visited = set()
	pathlen = defaultdict(lambda: float('inf'))
	cur_pathlen = 0
	p = [0] * 26

	for d, n in moves:
		if d in lower:
			i = ord(d) - ord('a')

			for _ in range(n):
				p[i] -= 1
				cur_pathlen += 1
				tp = tuple(p)
				pathlen[tp] = min(pathlen[tp], cur_pathlen)
				visited.add(tp)
		else:
			i = ord(d) - ord('A')

			for _ in range(n):
				p[i] += 1
				cur_pathlen += 1
				tp = tuple(p)
				pathlen[tp] = min(pathlen[tp], cur_pathlen)
				visited.add(tp)

	return visited, pathlen

def manhattan(*coords):
	return sum(abs(i - j) for i, j in zip(coords[:26], coords[26:]))


lines = open('up.txt').readlines()

all_visited = []
all_pathlen = []

for l in lines:
	visited, pathlen = get_visited(map(make_move, l.split(',')))
	all_visited.append(visited)
	all_pathlen.append(pathlen)

intersections = set.intersection(*all_visited)
min_distance = min(manhattan(*p, *(0,)*26) for p in intersections)

assert min_distance == 3247
print('Part 1:', min_distance)

shortest_path = min(sum(l[p] for l in all_pathlen) for p in intersections)

assert shortest_path == 96120
print('Part 2:', shortest_path)
