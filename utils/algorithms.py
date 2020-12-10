__all__ = [
	'INFINITY',
	'neighbors4', 'neighbors4x', 'neighbors8',
	'grid_find_adjacent', 'graph_from_grid', 'grid_bfs', 'grid_bfs_lru',
	'dijkstra', 'dijkstra_lru', 'dijkstra_path', 'dijkstra_path_lru',
	'dijkstra_all', 'dijkstra_all_paths',
	'bellman_ford',
	'bisection', 'binary_search',
	'knapsack'
]

import heapq
from collections import deque, defaultdict
from functools import lru_cache
from bisect import bisect_left
from math import inf as INFINITY

# Maximum cache size used for memoization with lru_Cache
MAX_CACHE_SIZE = 256 * 2**20 # 256Mi entries -> ~4GiB if one entry is 32 bytes

def _grid_neighbors(deltas):
	'''Create a generator function for finding neighbors in a 2D grid.

	Given a specific list of deltas, returns a generator function to find
	neighbors in a 2D grid (matrix) looking in nearby cells obtained adding each
	delta to the source.
	'''
	def g(grid, r, c, avoid='#'):
		'''Get neighbors of a cell in a 2D grid (matrix) i.e. list of lists or
		similar. Performs bounds checking.
		'''
		width  = len(grid)
		height = len(grid[0])

		for dr, dc in deltas:
			rr, cc = (r + dr, c + dc)
			if 0 <= rr < width and 0 <= cc < height:
				if grid[rr][cc] not in avoid:
					yield (rr, cc)

	return g

neighbors4  = _grid_neighbors(((1, 0), (-1, 0), (0, 1), (0, -1)))
neighbors4x = _grid_neighbors(((1, 1), (1, -1), (-1, 1), (-1, -1)))
neighbors8  = _grid_neighbors(((1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)))

def grid_find_adjacent(grid, src, find, avoid='#', coords=False, get_neighbors=neighbors4):
	'''Find edges to reachable nodes in a character grid (2D matrix) given a
	source and a set of characters to consider as nodes.

	src: (row, col) to start searching from.
	find: characters to consider as nodes.
	avoid: characters to consider walls.
	Anyting else is considered open space.

	The get_neighbors function is used to determine the neighbors of a cell.
	If coords=False (default), yields edges in the form (char, dist), otherwise
	in the form ((row, col, char), dist).

	Uses breadth-first search.
	'''
	visited = {src}
	queue   = deque()

	for n in neighbors4(grid, *src, avoid):
		queue.append((1, n))

	while queue:
		dist, node = queue.popleft()

		if node not in visited:
			visited.add(node)
			r, c = node

			if grid[r][c] in find:
				if coords:
					yield ((r, c, grid[r][c]), dist)
				else:
					yield (grid[r][c], dist)

				continue

			for neighbor in filter(lambda n: n not in visited, get_neighbors(grid, *node)):
				queue.append((dist + 1, neighbor))

def graph_from_grid(grid, find, avoid='#', coords=False, get_neighbors=neighbors4):
	'''Reduce a character grid (2D matrix) to an undirected graph by finding
	nodes and calculating their distance to others.

	find: characters to find in the grid which will be nodes of the graph.
	avoid: characters to consider walls.
	Anything else is considered open space.

	The get_neighbors function is used to determine the neighbors of a cell.
	If coord=False (default), nodes of the graph will be represented by the
	found character only, otherwise by a tuple of the form (row, col, char).

	Resulting graph will be of the form {node: [(dist, node)]}.
	'''
	graph = {}

	for r, row in enumerate(grid):
		for c, char in enumerate(row):
			if char in find:
				node = (r, c, char) if coords else char
				graph[node] = list(grid_find_adjacent(grid, (r, c), find, avoid, coords, get_neighbors))

	return graph

def grid_bfs(grid, src, dst, get_neighbors=neighbors4):
	'''Find the length of any path from src to dst in grid using breadth-first
	search, where grid is a 2D matrix i.e. list of lists or similar.

	src and dst are tuples in the form (row, col).
	The get_neighbors function is used to determine the neighbors of a cell.

	For memoization, use: bfs = bfs_grid_lru(grid); bfs(src, dst).
	'''
	queue   = deque([(0, src)])
	visited = set()

	while queue:
		dist, rc = queue.popleft()

		if rc == dst:
			return dist

		if rc not in visited:
			visited.add(rc)

			for n in filter(lambda n: n not in visited, neighbors4(grid, *rc)):
				queue.append((dist + 1, n))

	return INFINITY

def grid_bfs_lru(grid, get_neighbors=neighbors4):
	@lru_cache(MAX_CACHE_SIZE)
	def wrapper(src, dst):
		nonlocal grid, get_neighbors
		return bfs_grid(grid, src, dst, get_neighbors)
	return wrapper

def dijkstra(G, src, dst, get_neighbors=None):
	'''Find the length of the shortest path from src to dst in G using
	Dijkstra's algorithm.

	G is a "graph dictionary": {src: [(dst, weight)]}.
	The get_neighbors function is used to determine the neighbors of a node
	(defaults to G.get).

	For memoization, use: djk = dijkstra_lru(G); djk(src, dst).
	'''
	if get_neighbors is None:
		get_neighbors = G.get

	distance = defaultdict(lambda: INFINITY, {src: 0})
	queue    = [(0, src)]
	visited  = set()

	while queue:
		dist, node = heapq.heappop(queue)

		if node == dst:
			return dist

		if node not in visited:
			visited.add(node)
			neighbors = get_neighbors(node)

			if not neighbors:
				continue

			for neighbor, weight in filter(lambda n: n[0] not in visited, neighbors):
				new_dist = dist + weight

				if new_dist < distance[neighbor]:
					distance[neighbor] = new_dist
					heapq.heappush(queue, (new_dist, neighbor))

	return INFINITY

def dijkstra_lru(G, get_neighbors=None):
	@lru_cache(MAX_CACHE_SIZE)
	def wrapper(src, dst):
		nonlocal G, get_neighbors
		return dijkstra(G, src, dst, get_neighbors)
	return wrapper

def dijkstra_path(G, src, dst, get_neighbors=None):
	'''Find the shortest path from src to dst in G and its length using
	Dijkstra's algorithm. Returns a tuple (path, length).

	G is a "graph dictionary": {src: [(dst, weight)]}. The get_neighbors
	function is used to determine the neighbors of a node (defaults to G.get).

	For memoization, use: djk = dijkstra_path_lru(G); djk(src, dst).
	'''
	if get_neighbors is None:
		get_neighbors = G.get

	distance = defaultdict(lambda: INFINITY, {src: 0})
	queue    = [(0, src, (src,))]
	visited  = set()

	while queue:
		dist, node, path = heapq.heappop(queue)

		if node == dst:
			return path, dist

		if node not in visited:
			visited.add(node)
			neighbors = get_neighbors(node)

			if not neighbors:
				continue

			for neighbor, weight in filter(lambda n: n[0] not in visited, neighbors):
				new_dist = dist + weight

				if new_dist < distance[neighbor]:
					distance[neighbor] = new_dist
					heapq.heappush(queue, (new_dist, neighbor, path + (neighbor,)))

	return (), INFINITY

def dijkstra_path_lru(G, get_neighbors=None):
	@lru_cache(MAX_CACHE_SIZE)
	def wrapper(src, dst):
		nonlocal G, get_neighbors
		return dijkstra_path(G, src, dst, get_neighbors)
	return wrapper

def dijkstra_all(G, src, get_neighbors=None):
	'''Find the length of all the shortest path from src to any reachable node
	in G using Dijkstra's algorithm.

	Reurns a defaultdict {node: distance}, where unreachable nodes have
	distance=INFINITY.

	G is a "graph dictionary": {src: [(dst, weight)]}. The get_neighbors
	function is used to determine the neighbors of a node (defaults to G.get).
	'''
	if get_neighbors is None:
		get_neighbors = G.get

	distance = defaultdict(lambda: INFINITY, {src: 0})
	queue    = [(0, src)]
	visited  = set()

	while queue:
		dist, node = heapq.heappop(queue)

		if node not in visited:
			visited.add(node)
			neighbors = get_neighbors(node)

			if not neighbors:
				continue

			for neighbor, weight in filter(lambda n: n[0] not in visited, neighbors):
				new_dist = dist + weight

				if new_dist < distance[neighbor]:
					distance[neighbor] = new_dist
					heapq.heappush(queue, (new_dist, neighbor))

	return distance

def dijkstra_all_paths(G, src, get_neighbors=None):
	'''Find all the shortest paths from src to any reachable node in G and their
	lengths Dijkstra's algorithm.

	Returns a defaultdict {node: (path, length)}, where unreachable nodes have
	path=() and length=INFINITY.

	G is a "graph dictionary": {src: [(dst, weight)]}. The get_neighbors
	function is used to determine the neighbors of a node (defaults to G.get).
	'''
	if get_neighbors is None:
		get_neighbors = G.get

	pd      = defaultdict(lambda: ((), INFINITY), {src: ((src,), 0)})
	queue   = [(0, src, (src,))]
	visited = set()

	while queue:
		dist, node, path = heapq.heappop(queue)

		if node not in visited:
			visited.add(node)
			neighbors = get_neighbors(node)

			if not neighbors:
				continue

			for neighbor, weight in filter(lambda n: n[0] not in visited, neighbors):
				new_dist = dist + weight

				if new_dist < pd[neighbor][1]:
					new_path = path + (neighbor,)
					pd[neighbor] = (new_path, new_dist)
					heapq.heappush(queue, (new_dist, neighbor, new_path))

	return pd

def bellman_ford(G, src):
	'''Find all the shortest paths from src to any reachable node in G and their
	lengths using the Bellman-Ford algorithm. IMPORTANT: all nodes of the graph
	should be in G as keys!

	G is a "graph dictionary": {src: [(dst, weight)]}.

	Returns two defaultdicts: distance, previous.

	distance[node]: length of the shortest path from src to node
		default	to INFINITY for unreachable nodes.
	previous[node]: previous node in the shortest path from src to node
		default to None for unreachable nodes.
	'''
	distance = defaultdict(lambda: INFINITY, {src: 0})
	previous = defaultdict(lambda: None)

	# This needs to run exactly num_of_nodes - 1 times. If G does not have all
	# nodes as keys this will run fewer times and produce wrong results.
	for _ in range(len(G) - 1):
		for node, edges in G.items():
			for neighbor, weight in edges:
				new_dist = distance[node] + weight

				if new_dist < distance[neighbor]:
					distance[neighbor] = new_dist
					previous[neighbor] = node

	for _ in range(len(G) - 1):
		for node, edges in G.items():
			for neighbor, weight in edges:
				if distance[node] + weight < distance[neighbor]:
					raise Exception('Bellman-Ford on graph containing negative-weight cycles')

	return distance, previous

def bisection(fn, y, lo=None, hi=None, tolerance=1e-9, upper=False):
	'''Find a value x in the range [hi, lo] such that f(x) approximates y.

	If y is an int, find an exact match for x such that y == fn(x); return None
	on failure.

	If y is a float, find a lower bound for x instead (or upper bound if
	upper=True); in this case, the search cannot fail. It is up to the caller to
	supply meaningful values for lo and hi.

	If not supplied, lo and hi are found through exponential search.
	'''
	if type(y) not in (int, float):
		raise TypeError('y must be int or float, got {}'.format(type(y)))

	if lo is None:
		# Optimistic check
		if fn(0) <= y:
			lo = 0

		lo = -1
		while fn(lo) > y:
			lo *= 2

	if hi is None:
		hi = 1
		while fn(hi) < y:
			hi *= 2

	if type(y) is int:
		while lo <= hi:
			x = (lo + hi) // 2
			v = fn(x)

			if v > y:
				hi = x - 1
			elif v < x:
				lo = x + 1
			else:
				return x

		return None

	if type(y) is not float:
		raise TypeError('y must be int or float, got {}'.format(type(y).__name__))

	if upper:
		while hi - lo >= tolerance:
			x = (lo + hi) / 2

			if fn(x) < y:
				lo = x
			else:
				hi = x

		return hi

	while hi - lo >= tolerance:
		x = (lo + hi) / 2

		if fn(x) > y:
			hi = x
		else:
			lo = x

	return lo

def binary_search(a, x):
	'''Find the index of x in the sorted iterable a using binary search. Returns
	-1 if x not in a.

	Note: a must be indexable.
	'''
	# https://docs.python.org/3/library/bisect.html#searching-sorted-lists
	i = bisect_left(a, x)
	if i != len(a) and a[i] == x:
		return i
	return -1

def knapsack(items, weight_limit):
	'''0-1 knapsack: find the best subset of items to choose to get the maximum
	total value with the given total weight limit.

	items is a dictionary in the form {key: (value, weight)}

	Returns a tuple (best, chosen) where best is the maximum total value
	achievable and chosen is a list of keys representing chosen items.
	'''
	# Solve w/ dynamic programming, number items arbitrarily from 1 to N
	# creating a mapping {index: key}
	key = {i: k for i, k in enumerate(items, 1)}

	# best(n, wl) -> best score choosing amongst the first n elements
	# with a total weight limit of wl
	@lru_cache(MAX_CACHE_SIZE)
	def best(n, wl):
		if n == 0 or wl <= 0:
			return 0

		v, w = items[key[n]]
		if w > wl:
			return best(n - 1, wl)

		return max(best(n - 1, wl), best(n - 1, wl - w) + v)

	n = len(items)
	wl = weight_limit
	sol = best(n, wl)
	chosen = []

	for n in range(n, 0, -1):
		if best(n, wl) != best(n - 1, wl):
			chosen.append(key[n])
			wl -= items[key[n]][1]

	return sol, chosen

def knapsack_bounded():
	raise NotImplementedError('TODO?')

def knapsack_unbounded():
	raise NotImplementedError('TODO?')
