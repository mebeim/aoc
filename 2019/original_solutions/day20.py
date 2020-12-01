#!/usr/bin/env python3

from utils.all import *

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

@lru_cache(2**20)
def key_from_pos(grid, r, c):
	if grid[r][c] != '.':
		return None

	valid = False
	for nr, nc in neighbors4(grid, r, c):
		v = grid[nr][nc]
		if 'A' <= v <= 'Z':
			valid = True
			break

	if not valid:
		return None

	valid = False
	for nnr, nnc in neighbors4(grid, nr, nc):
		vv = grid[nnr][nnc]
		if 'A' <= vv <= 'Z':
			valid = True
			break

	assert valid

	if nnr > nr or nnc > nc:
		key = v + vv
	else:
		key = vv + v

	return key + '(' + str(r) + ',' + str(c) +')'

def neighbors4(grid, r, c):
	for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
		rr, cc = (r + dr, c + dc)
		if 0 <= rr < len(grid) and 0 <= cc < len(grid[rr]):
			if grid[rr][cc] not in '# ':
				yield (rr, cc)


def dijkstra(G, src, dst):
	distance  = defaultdict(lambda: float('inf'))
	queue     = []
	visited = set()

	queue.append((0, src, [src]))
	distance[src] = 0

	while queue:
		dist, node, path = heapq.heappop(queue)

		if node not in visited:
			if node == dst:
				return dist, path

			visited.add(node)

			for neighbor in filter(lambda p: p not in visited, G[node]):
				new_dist = dist + G[node][neighbor]

				if new_dist < distance[neighbor]:
					distance[neighbor] = new_dist
					heapq.heappush(queue, (new_dist, neighbor, path + [neighbor]))

	return float('inf'), None

def find_adjacent(grid, src, src_key):
	visited = {src}
	queue   = deque()
	found   = {}

	for n in neighbors4(grid, *src):
		queue.append((1, n))

	while queue:
		dist, node = queue.popleft()

		if node not in visited:
			visited.add(node)
			key = key_from_pos(grid, *node)

			if key is not None and key != src_key and (key not in found or found[key] > dist):
				found[key] = dist
				continue

			for neighbor in filter(lambda n: n not in visited, neighbors4(grid, *node)):
				queue.append((dist + 1, neighbor))

	return found

def build_graph(grid):
	graph    = {}

	for r, row in enumerate(grid):
		for c in range(len(row)):
			key = key_from_pos(grid, r, c)

			if key is not None:
				graph[key] = find_adjacent(grid, (r, c), key)

	return graph


grid = tuple(l.strip('\n') for l in fin)
# print(find_adjacent(grid, (8, 0)))

G = build_graph(grid)
# dump_dict(G)

for k in G:
	if k.startswith('AA'):
		start = k
	if k.startswith('ZZ'):
		end = k

# eprint(start, end)

for k1 in G:
	for k2 in G:
		if k1 != k2:
			if k1[:2] == k2[:2]:
				G[k1][k2] = 1
				G[k2][k1] = 1

ans, path = dijkstra(G, start, end)
# eprint(ans)
# dump_iterable(path)
advent.submit_answer(1, ans)


################################################################################
# part 2... don't you love duplicated code?
################################################################################

@lru_cache(2**20)
def recursive_neighbors(src):
	depth = int(src[3:])
	ksrc = src[:3] + '0'
	res = []

	depth0_neighbors = G[ksrc]

	if src[2] == 'i':
		res.append((src[:2] + 'o' + str(depth + 1), 1))

	if depth == 0:
		for k, d in depth0_neighbors:
			if k[2] == 'i' or k == ENTRANCE or k == EXIT:
				res.append((k, d))
	else:
		sdepth = str(depth)

		if src[2] == 'o':
			res.append((src[:2] + 'i' +  str(depth - 1), 1))

		for k, d in depth0_neighbors:
			if k != ENTRANCE and k != EXIT:
				res.append((k[:3] + sdepth, d))

	# if src == 'CKo1':
	# 	print(ksrc, depth0_neighbors)
	# 	print(src, res)

	return tuple(res)

@lru_cache(2**20)
def key_from_pos2(grid, r, c):
	if grid[r][c] != '.':
		return None

	valid = False
	for nr, nc in neighbors4(grid, r, c):
		v = grid[nr][nc]
		if 'A' <= v <= 'Z':
			valid = True
			break

	if not valid:
		return None

	valid = False
	for nnr, nnc in neighbors4(grid, nr, nc):
		vv = grid[nnr][nnc]
		if 'A' <= vv <= 'Z':
			valid = True
			break

	assert valid

	if nnr > nr or nnc > nc:
		key = v + vv
	else:
		key = vv + v

	if nnr == 0 or nnc == 0 or nnr == MAXROW or nnc == MAXCOLUMN or nr == 0 or nc == 0 or nr == MAXROW or nc == MAXCOLUMN:
		return key + 'o0'

	return key + 'i0'


def dijkstra2(G, src, dst):
	distance  = defaultdict(lambda: float('inf'))
	queue     = [(0, src, [src])]
	# queue     = [(0, src)]
	visited   = set()

	distance[src] = 0

	while queue:
		dist, node, path = heapq.heappop(queue)
		# dist, node = heapq.heappop(queue)

		if node not in visited:
			if node == dst:
				return dist, path
				# return dist

			visited.add(node)

			for neighbor, weight in filter(lambda p: p[0] not in visited, recursive_neighbors(node)):
				new_dist = dist + weight

				if new_dist < distance[neighbor]:
					distance[neighbor] = new_dist
					heapq.heappush(queue, (new_dist, neighbor, path + [neighbor]))
					# heapq.heappush(queue, (new_dist, neighbor))

	return float('inf'), None
	# return float('inf')

def find_adjacent2(grid, src, src_key):
	visited = {src}
	queue   = deque()
	found   = []

	for n in neighbors4(grid, *src):
		queue.append((1, n))

	while queue:
		dist, node = queue.popleft()

		if node not in visited:
			visited.add(node)
			key = key_from_pos2(grid, *node)

			if key is not None and key != src_key and key not in found:
				found.append((key, dist))
				continue

			for neighbor in filter(lambda n: n not in visited, neighbors4(grid, *node)):
				queue.append((dist + 1, neighbor))

	return found

def build_graph2(grid):
	graph    = {}

	for r, row in enumerate(grid):
		for c in range(len(row)):
			key = key_from_pos2(grid, r, c)

			if key is not None:
				graph[key] = find_adjacent2(grid, (r, c), key)

	return graph

ROWS = len(grid)
COLUMNS = len(grid[0])
MAXROW, MAXCOLUMN = ROWS-1, COLUMNS-1

G = build_graph2(grid)
# dump_dict(G)

for k in G:
	if k.startswith('AA'):
		ENTRANCE = k
	if k.startswith('ZZ'):
		EXIT = k


ans, path = dijkstra2(G, ENTRANCE, EXIT)
# eprint(ans)
# dump_iterable(path)

# 1007 wrong
advent.submit_answer(2, ans)
