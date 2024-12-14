#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 14)
fin = advent.get_input()

data = fin.read()
ints = extract_ints(data)

ans1 = ans2 = 0
robots = []
for i in range(0, len(ints), 4):
	px, py, vx, vy = ints[i:i + 4]
	robots.append((Vec(px,py), Vec(vx, vy)))


def quadrant(p, v, t=100, width=101, height=103):
	p = p + v * t
	x = p.x % width
	y = p.y % height

	if x <= width // 2 - 1:
		if y <= height // 2 - 1:
			return 'nw'
		if y >= height // 2 + 1:
			return 'sw'

	if x >= width // 2 + 1:
		if y <= height // 2 - 1:
			return 'ne'
		if y >= height // 2 + 1:
			return 'se'

	return None


counts = defaultdict(int)
for p, v in robots:
	q = quadrant(p, v)
	if q is None:
		continue

	counts[q] += 1

ans1 = prod(counts.values())
advent.print_answer(1, ans1)


seen = set()
heuristic = defaultdict(int)


def show(robots, t, width=101, height=103):
	sparse = set()
	for p, v in robots:
		pp = p + v * t
		x = pp.x % width
		y = pp.y % height
		sparse.add((x,y))

	# f = frozenset(sparse)
	# if f in seen:
	# 	sys.exit(0)
	# seen.add(f)

	# eprint('-------------', t, '-------' * 15)
	# with open(f'{t:06}.txt', 'w') as f:
	# 	sys.stderr = f
	# 	dump_sparse_matrix(sparse)
	# 	f.flush()

	for x, y in sparse:
		for n in neighbors4_coords(x, y):
			if n in sparse:
				heuristic[t] += 1


for t in range(10469):
	show(robots, t)

# x = sorted(heuristic.items(), key=lambda i: i[::-1], reverse=True)
# dump_iterable(x[:100])

x = max(heuristic, key=heuristic.get)

# Highest euristic wins
advent.print_answer(2, x)
