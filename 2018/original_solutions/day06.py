#!/usr/bin/env python3

from utils import advent
from collections import namedtuple, defaultdict

advent.setup(2018, 6)
fin = advent.get_input()

##################################################

def dist(p1, x, y):
	return abs(p1.x - x) + abs(p1.y - y)

def compute_counts(bigbound):
	counts = defaultdict(int)

	for i in range(-bigbound, bigbound):
		if i % 100 == 0:
			print(str(i) + '...')

		for j in range(-bigbound, bigbound):
			min_dist = 999999999
			nearest = None
			ignore = False

			for p in pts:
				d = dist(p, i, j)

				if d < min_dist:
					min_dist = d
					nearest = p
					ignore = False
				elif d == min_dist:
					ignore = True

			if not ignore:
				counts[nearest] += 1

	return counts

def count_within_distance(limit):
	tot = 0

	for i in range(0, 500):
		if i % 100 == 0:
			print(str(i) + '~~~')

		for j in range(0, 500):
			totdist = sum(dist(p, i, j) for p in pts)

			if totdist < limit:
				tot += 1

	return tot


P = namedtuple('P', ['x', 'y'])

pts = []
for l in fin:
	pts.append(P(*map(int, l.split(','))))

print(pts)

# compute_counts runs for ages, comment out everything
# from here to advent.submit_answer(1, ...) for part 2

cnts1 = compute_counts(500)
cnts2 = compute_counts(600)

# with open('oo1', 'w') as f:
# 	for p in sorted(cnts, key=cnts.get):
# 		f.write('{:<6d} {}'.format(cnts[p], p))
# 		f.write('\n')

# with open('oo2', 'w') as f:
# 	for p in sorted(cnts2, key=cnts2.get):
# 		f.write('{:<6d} {}'.format(cnts2[p], p))
# 		f.write('\n')

best_count = 0
best = None

for p in pts:
	c1, c2 = cnts1[p], cnts2[p]

	if c1 == c2:
		if c1 > best_count:
			best_count = c1
			best = p

assert best_count == 4215

advent.submit_answer(1, best_count)

ans2 = count_within_distance(10000)

advent.submit_answer(2, ans2)
