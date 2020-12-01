#!/usr/bin/env python3

from utils.all import *
from functools import lru_cache

advent.setup(2018, 22)
fin = advent.get_input()
# print(*fin)
timer_start()

##################################################

@lru_cache(maxsize=2**18)
def geo(x, y):
	if (x, y) in ((0, 0), global_target):
		return 0
	if y == 0:
		return x*16807
	if x == 0:
		return y*48271
	return erosion(x-1, y) * erosion(x, y-1)

def erosion(x, y):
	return (geo(x, y) + depth) % 20183

def risk(x, y):
	return erosion(x, y) % 3

@lru_cache(maxsize=4096)
def adj(pos):
	xy, tool = pos
	x, y = xy

	# for t in canuse[cave[xy]]:
	# 	if t != tool:
	# 		yield xy, t

	yield xy, othertool[cave[xy], tool]

	for dx, dy in ((0, 1), (0, -1), (1, 0), (-1, 0)):
		a = (x + dx, y + dy)

		if a in cave and tool in canuse[cave[a]]:
			yield a, tool

@lru_cache(maxsize=4096)
def dist(a, b):
	# log('calc dist{} --- {}\n', a, b)
	axy, at = a
	bxy, bt = b

	if axy == bxy and at == bt:
		return 0

	if at == bt:
		return 1

	if axy == bxy:
		return 7

	raise Exception('wat')

@lru_cache(maxsize=4096)
def reachable(pos):
	for a in adj(pos):
		yield a, dist(pos, a)

def explore(source, targets):
	q = set()
	distances = {}

	for v, r in cave.items():
		for t in canuse[r]:
			distances[v, t] = 1e99
			q.add((v, t))

	distances[source] = 0

	while q:
		u = min(q, key=distances.__getitem__)
		q.remove(u)

		log('node {} dist {}\n', u, distances[u])

		for v, delta in reachable(u):
			log('  can reach {} in {} minutes\n', v, delta)

			alt = distances[u] + delta
			if alt < distances[v]:
				distances[v] = alt

	return min(distances[t] for t in targets)


ROCKY, WET, NARROW = range(3)
TORCH, CLIMBGEAR, NEITHER = 'TCN'#range(3)
TOOLS = (TORCH, CLIMBGEAR, NEITHER)

canuse = {
	ROCKY: {CLIMBGEAR, TORCH},
	WET: {CLIMBGEAR, NEITHER},
	NARROW: {TORCH, NEITHER}
}

othertool = {
	(ROCKY, TORCH): CLIMBGEAR,
	(ROCKY, CLIMBGEAR): TORCH,
	(WET, NEITHER): CLIMBGEAR,
	(WET, CLIMBGEAR): NEITHER,
	(NARROW, TORCH): NEITHER,
	(NARROW, NEITHER): TORCH
}

depth, tx, ty = get_ints(fin, True)
global_target = (tx, ty)
log('depth: {} target: {}\n', depth, global_target)

tot = 0
cavew, caveh = 8*tx, 8*ty
cave = {}
# cavemap = []

for x in range(cavew):
	# if 0 <= x <= cavew:
	# 	cavemap.append([])

	for y in range(caveh):
		cave[x, y] = risk(x, y)
		# for tool in canuse[r]:
		# 	cave[x, y, tool] = r
		# if 0 <= y <= ty + 10:
		# 	cavemap[x].append('.=|'[r])


		if 0 <= x <= tx and 0 <= y <= ty:
			tot += cave[x, y]

# log('T: {}\n', cavemap[tx][ty])
# cavemap[tx][ty] = 'T'
# dump_char_matrix(cavemap, transpose=True)

# 68796924 not right
# 76502334 not right
advent.submit_answer(1, tot)


source = ((0, 0), TORCH)
targets = set()

for tool in canuse[cave[tx, ty]]:
	targets.add(((tx, ty), tool))

graph = nx.Graph()
graph.add_node(source)

graph.add_edge(source, (source[0], othertool[cave[source[0]], source[1]]), weight=7)

for xy, r in cave.items():
	for t in canuse[r]:
		n = (xy, t)
		graph.add_node(n)

		for v, delta in reachable(n):
			graph.add_edge(n, v, weight=delta)

# dump_iterable(reachable(source))
# ans = explore(source, targets)

pathlens = nx.single_source_dijkstra_path_length(graph, source)
minimum = 1e99

for target in targets:
	# log('{}: {}\n', target, pathlens[target])
	# dump_iterable(nx.dijkstra_path(graph, source, target))
	# log('-'*50 + '\n')

	cur = pathlens[target]

	if target[1] != TORCH:
		cur += 7

	if cur < minimum:
		minimum = cur

	# sys.exit()

# 1052 too high
advent.submit_answer(2, minimum)
