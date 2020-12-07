import heapq
from collections import deque, defaultdict
from functools import lru_cache
from bisect import bisect_left
from math import inf as INFINITY

__all__ = [
	'INFINITY',
	'neighbors4', 'neighbors4x', 'neighbors8',
	'bfs_grid', 'bfs_grid_lru',
	'dijkstra', 'dijkstra_lru', 'dijkstra_path', 'dijkstra_path_lru',
	'bisection', 'binary_search'
]

# Cache size used for memoization with lru_Cache
CACHE_SIZE = 256 * 2**20 # ~256M entries

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

def find_adjacent(grid, src):
	raise NotImplementedError('TODO')

	visited = {src}
	queue   = deque()
	found   = []

	for n in neighbors4(grid, *src):
		queue.append((1, n))

	while queue:
		dist, node = queue.popleft()

		if node not in visited:
			visited.add(node)

			portal = portal_from_grid(grid, *node)

			if portal is not None:
				found.append((portal, dist))
				continue

			for neighbor in filter(lambda n: n not in visited, neighbors4(grid, *node)):
				queue.append((dist + 1, neighbor))

	return found

def build_graph(grid):
	raise NotImplementedError('TODO')

	graph = {}

	for r, row in enumerate(grid):
		for c in range(len(row)):
			key = portal_from_grid(grid, r, c)

			if key is not None:
				graph[key] = find_adjacent(grid, (r, c))

	return graph

def bfs_grid(grid, src, dst):
	'''Find the length of any path from src to dst in grid using breadth-first
	search, where grid is a 2D matrix i.e. list of lists or similar.

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

def bfs_grid_lru(grid):
	@lru_cache(CACHE_SIZE)
	def wrapper(src, dst):
		return bfs_grid(grid, src, dst)
	return wrapper

def dijkstra(G, src, dst, get_neighbors=None):
	'''Find the length of the shortest path from src to dst in G using
	Dijkstra's algorithm.

	G is a "graph dictionary": {src: [(dst, weight)]}. The get_neighbors
	function is used to determine the neighbors of a node (defaults to G.get).

	For memoization, use: djk = dijkstra_lru(G); djk(src, dst).
	'''
	if get_neighbors is None:
		get_neighbors = G.get

	distance = defaultdict(lambda: INFINITY)
	queue    = [(0, src)]
	visited  = set()

	distance[src] = 0

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

def dijkstra_lru(G):
	@lru_cache(CACHE_SIZE)
	def wrapper(src, dst, get_neighbors=None):
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

	distance = defaultdict(lambda: INFINITY)
	queue    = [(0, src, (src,))]
	visited  = set()

	distance[src] = 0

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

	return None, INFINITY

def dijkstra_path_lru(G):
	@lru_cache(CACHE_SIZE)
	def wrapper(src, dst, get_neighbors=None):
		return dijkstra_path(G, src, dst, get_neighbors)
	return wrapper

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

# https://docs.python.org/3/library/bisect.html#searching-sorted-lists
def binary_search(a, x):
	'''Find the index of x in the sorted iterable a using binary search. Return
	-1 if x not in a.

	Note: a must be indexable.
	'''
	i = bisect_left(a, x)
	if i != len(a) and a[i] == x:
		return i
	return -1
