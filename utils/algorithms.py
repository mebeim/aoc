__all__ = [
	'INFINITY',
	'grid_neighbors_gen', 'grid_neighbors_values_gen',
	'neighbors4', 'neighbors4x', 'neighbors8',
	'neighbors4_values', 'neighbors4x_values', 'neighbors8_values',
	'neighbors4_coords', 'neighbors4x_coords', 'neighbors8_coords',
	'grid_find_adjacent', 'graph_from_grid', 'grid_bfs', 'grid_bfs_lru',
	'bfs', 'connected_components',
	'dijkstra', 'dijkstra_lru', 'dijkstra_path', 'dijkstra_path_lru',
	'dijkstra_all', 'dijkstra_all_paths',
	'bellman_ford', 'floyd_warshall', 'kruskal', 'toposort', 'lex_toposort',
	'bisection', 'binary_search',
	'knapsack'
]

import heapq
from collections import deque, defaultdict
from functools import lru_cache
from bisect import bisect_left
from math import inf as INFINITY
from itertools import filterfalse
from operator import itemgetter
from itertools import product
from typing import TypeVar, Any, Iterable, Iterator, Callable, Union, Optional
from typing import List, Tuple, Dict, DefaultDict, Set, Deque, Sequence, Container

from .data_structures import UnionFind

T = TypeVar('T')

Grid2D              = Sequence[Sequence[Any]]
Coord2D             = Tuple[int,int]
WeightedGraphDict   = Dict[T,List[Tuple[T,int]]]
UnweightedGraphDict = Dict[T,List[T]]
GraphDict           = Union[WeightedGraphDict,UnweightedGraphDict]
GridNeighborsFunc   = Callable[[Grid2D,int,int,Container],Iterator[Coord2D]]
GraphNeighborsFunc  = Callable[[GraphDict,T],Iterator[T]]
Distance            = Union[int,float]
IntOrFloat          = Union[int,float]

# Maximum cache size used for memoization with lru_cache
MAX_CACHE_SIZE = 256 * 2**20 # 256Mi entries -> ~8GiB if one entry is 32 bytes

def grid_neighbors_gen(deltas: Iterable[Coord2D]) -> GridNeighborsFunc:
	'''Create a generator function yielding coordinates of neighbors of a given
	cell in a grid (2D matrix) given a list of deltas to apply to the source
	coordinates to get neighboring cells.
	'''
	def g(grid: Grid2D, r: int, c: int, avoid: Container=()) -> Iterator[Coord2D]:
		'''Yield coordinates of neighbors of a cell in a 2D grid (matrix) i.e.
		list of lists or similar. Performs bounds checking. Grid is assumed to
		be rectangular.
		'''
		maxr = len(grid) - 1
		maxc = len(grid[0]) - 1
		check = r == 0 or r == maxr or c == 0 or c == maxc

		if check:
			for dr, dc in deltas:
				rr, cc = (r + dr, c + dc)
				if 0 <= rr <= maxr and 0 <= cc <= maxc:
					if grid[rr][cc] not in avoid:
						yield (rr, cc)
		else:
			for dr, dc in deltas:
				rr, cc = (r + dr, c + dc)
				if grid[rr][cc] not in avoid:
					yield (rr, cc)

	return g

def grid_neighbors_values_gen(deltas: Iterable[Coord2D]) \
		-> Callable[[Grid2D,int,int,Container],Iterator[Any]]:
	'''Create a generator function yielding values of neighbors of a given cell
	in a grid (2D matrix) given a list of deltas to apply to the source
	coordinates to get neighboring cells.
	'''
	g = grid_neighbors_gen(deltas)

	def v(grid: Grid2D, r: int, c: int, avoid: Container=()) -> Iterator[Any]:
		'''Yield values of neighbors of a cell in a 2D grid (matrix) i.e. list
		of lists or similar. Performs bounds checking. Grid is assumed to be
		rectangular.
		'''
		for rr, cc in g(grid, r, c, avoid):
			yield grid[rr][cc]

	return v

def neighbors_coords_gen(deltas: Iterable[Coord2D]) \
		-> Callable[[int,int],Iterator[Coord2D]]:
	'''Create a generator function yielding coordinates of neighbors of a given
	cell in a hypotetical grid (2D matrix), given a list of deltas to apply to
	the source coordinates.

	Useful for cases where bound-checking is not needed, like sparse matrices.
	'''
	def neighbor_coords(r: int, c: int) -> Iterator[Coord2D]:
		'''Yield hypotetical coordinates of neighbors of a cell in a 2D grid
		(matrix) i.e. list of lists or similar. No grid is given. Does NOT
		perform any bounds checking.
		'''
		for dr, dc in deltas:
			yield r + dr, c + dc

	return neighbor_coords

# These return coords, take a grid and do bound-check + avoid set check
neighbors4  = grid_neighbors_gen(((-1, 0), (0, -1), (0, 1), (1, 0)))
neighbors4x = grid_neighbors_gen(((-1, -1), (-1, 1), (1, -1), (1, 1)))
neighbors8  = grid_neighbors_gen(((-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)))

# These return values, take a grid and do bound-check + avoid set check
neighbors4_values  = grid_neighbors_values_gen(((-1, 0), (0, -1), (0, 1), (1, 0)))
neighbors4x_values = grid_neighbors_values_gen(((-1, -1), (-1, 1), (1, -1), (1, 1)))
neighbors8_values  = grid_neighbors_values_gen(((-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)))

# These return coords, don't take a grid and therefore do no bound-check and no avoid set check
neighbors4_coords  = neighbors_coords_gen(((-1, 0), (0, -1), (0, 1), (1, 0)))
neighbors4x_coords = neighbors_coords_gen(((-1, -1), (-1, 1), (1, -1), (1, 1)))
neighbors8_coords  = neighbors_coords_gen(((-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)))

def grid_find_adjacent(grid: Grid2D, src: Coord2D, find: Container,
		avoid: Container=(), coords: bool=False,
		get_neighbors: GridNeighborsFunc=neighbors4) \
		-> Union[Tuple[Tuple[int,int,Any],int],Tuple[Any,int]]:
	'''Find and yield edges to reachable nodes in grid (2D matrix) from src,
	considering the values in find as nodes, and the values in avoid as walls.

	- src: (row, col) to start searching from
	- find: values to consider nodes
	- avoid: values to consider walls
	- anyting else is considered open space
	- get_neighbors(grid, r, c, avoid) is called to determine cell neighbors

	If coords=False (default), yields edges in the form (node, dist), otherwise
	in the form ((row, col, node), dist). For a character grid, node will be a
	single character.

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

			for neighbor in filterfalse(visited.__contains__, get_neighbors(grid, *node)):
				queue.append((dist + 1, neighbor))

def graph_from_grid(grid: Grid2D, find: Container, avoid: Container=(),
		coords: bool=False, weighted: bool=False,
		get_neighbors: GridNeighborsFunc=neighbors4) \
		-> GraphDict:
	'''Reduce a grid (2D matrix) to an undirected graph by finding all nodes and
	calculating their distance to others. Note: can return a disconnected graph.

	- find: values to consider nodes of the graph
	- avoid: values to consider walls
	- anything else is considered open space
	- get_neighbors(grid, r, c, avoid) is called to determine cell neighbors

	If coord=False (default), nodes of the graph will be represented by the
	found value only, otherwise by a tuple of the form (row, col, char).

	Returns a "graph dictionary" of the form {src: [dst]} if weighted=False
	(default) or {src: [(dst, distance)]} if weighted=True.
	'''
	graph: GraphDict = {}

	for r, row in enumerate(grid):
		for c, x in enumerate(row):
			if x not in find:
				continue

			node = (r, c, x) if coords else x
			adj = grid_find_adjacent(grid, (r, c), find, avoid, coords, get_neighbors)

			if weighted:
				graph[node] = list(adj)
			else:
				graph[node] = list(map(itemgetter(0), adj))

	return graph

def grid_bfs(grid: Grid2D, src: Coord2D, dst: Union[Coord2D,None]=None,
		avoid: Container=(), get_neighbors: GridNeighborsFunc=neighbors4) \
		-> Union[Dict[Coord2D,Distance],Distance]:
	'''If dst is None (default): find all coordinates of grid reachable from src
	and their distance from src using breadth-first search. Returns a
	defaultdict {coord: distance}.

	If dst is not None: find and return the length of the path from src to dst
	in grid using breadth-first search. Returns INFINITY if no path is found.

	- grid is a 2D matrix i.e. list of lists or similar.
	- src and dst are tuples in the form (row, col)
	- get_neighbors(grid, r, c, avoid) is called to determine cell neighbors and
	  should yield coordinates

	For memoization use:
		gbfs = bfs_grid_lru(grid)
		distance = gbfs(src, dst)
	'''
	queue    = deque([src])
	distance = defaultdict(lambda: INFINITY, {src: 0})

	while queue:
		pos = queue.popleft()
		if dst is not None and pos == dst:
			break

		for n in filterfalse(distance.__contains__, get_neighbors(grid, *pos, avoid)):
			distance[n] = distance[pos] + 1
			queue.append(n)

	return distance if dst is None else distance[dst]

def grid_bfs_lru(grid: Grid2D, avoid: Container=(),
		get_neighbors: GridNeighborsFunc=neighbors4) \
		-> Callable[[Coord2D,Coord2D],Distance]:
	'''
	Memoized version of grid_bfs():
		gbfs = bfs_grid_lru(grid)
		distance = gbfs(src, dst)
	'''
	@lru_cache(MAX_CACHE_SIZE)
	def wrapper(src: Coord2D, dst: Coord2D) -> Union[Dict[Coord2D,Distance],Distance]:
		nonlocal grid, get_neighbors
		return grid_bfs(grid, src, dst, avoid, get_neighbors)
	return wrapper

def bfs(G: GraphDict, src: Any, dst: Union[Any,None]=None, weighted: bool=False,
		get_neighbors: Optional[GraphNeighborsFunc]=None) -> Union[Dict[Any,Distance],Distance]:
	'''If dst is None (default): find all nodes in G reachable from src and
	their distance from src using breadth-first search. Returns a defaultdict
	{node: distance}.

	If dst is not None: find and return the length of the path from src to dst
	in G using breadth-first search. Returns INFINITY if no path is found.

	G is a "graph dictionary" of the form {src: [dst]} or {src: [(dst, weight)]}
	if weighted=True.

	get_neighbors(node) is called to determine node neighbors (default is G.get)

	NOTE: for correct results in case of an undirected graph, all nodes must be
	present in G as keys.

	NOTE: by definition BFS will only find the length of the shortest path
	between two nodes if all edge weights are equal.
	'''
	if get_neighbors is None:
		get_neighbors = G.get

	queue    = deque([src])
	distance = defaultdict(lambda: INFINITY, {src: 0})

	while queue:
		node = queue.popleft()
		if dst is not None and node == dst:
			break

		neighbors = get_neighbors(node) or ()

		if weighted:
			for neighbor, weight in neighbors:
				if neighbor not in distance:
					distance[neighbor] = distance[node] + weight
					queue.append(neighbor)
		else:
			for neighbor in filterfalse(distance.__contains__, neighbors):
				distance[neighbor] = distance[node] + 1
				queue.append(neighbor)

	return distance if dst is None else distance[dst]

def connected_components(G: GraphDict, weighted: bool=False,
		get_neighbors: Optional[GraphNeighborsFunc]=None) -> List[Set[Any]]:
	'''Find and return a list of all the connected components of G.

	G is a "graph dictionary" of the form {src: [dst]} or {src: [(dst, weight)]}
	if weighted=True, in which case weights are ignored.

	get_neighbors(node) is called to determine node neighbors (default is G.get)

	Returns a list of sets each representing the nodes of a connected component.

	NOTE: for correct results in case of an undirected graph, all nodes must be
	present in G as keys.
	'''
	if get_neighbors is None:
		get_neighbors = G.get

	unweight = itemgetter(0) if weighted else lambda x: x
	uf = UnionFind(G)

	for node in G:
		uf.make_set(node)

		for neighbor in map(unweight, get_neighbors(node)):
			uf.make_set(neighbor)
			uf.union(node, neighbor)

	return uf.all_sets()

def dijkstra(G: WeightedGraphDict, src: Any, dst: Any,
		get_neighbors: Optional[GraphNeighborsFunc]=None) -> Distance:
	'''Find the length of the shortest path from src to dst in G using
	Dijkstra's algorithm.

	G is a weighted "graph dictionary" of the form {src: [(dst, weight)]}.

	For memoization use:
		djk = dijkstra_lru(G)
		distance = djk(src, dst)
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

def dijkstra_lru(G: WeightedGraphDict,
		get_neighbors: Optional[GraphNeighborsFunc]=None) \
		-> Callable[[Any,Any],Distance]:
	'''
	Memoized version of dijkstra():
		djk = dijkstra_lru(G)
		distance = djk(src, dst)
	'''
	@lru_cache(MAX_CACHE_SIZE)
	def wrapper(src: Any, dst: Any) -> Distance:
		nonlocal G, get_neighbors
		return dijkstra(G, src, dst, get_neighbors)
	return wrapper

def dijkstra_path(G: WeightedGraphDict, src: Any, dst: Any,
		get_neighbors: Optional[GraphNeighborsFunc]=None) \
		-> Tuple[Tuple[Any],Distance]:
	'''Find the shortest path from src to dst in G using Dijkstra's algorithm.

	G is a weighted "graph dictionary" of the form {src: [(dst, weight)]}
	get_neighbors(node) is called to determine node neighbors (default is G.get)

	Returns a tuple (shortest_path, length) where shortest_path is a tuple of
	the form (src, ..., dst). If no path is found, the result is ((), INFINITY).

	NOTE that the returned length is the length of the shortest path (i.e. sum
	of edge weights along the path), not the number of nodes in the path.

	For memoization use:
		djk = dijkstra_path_lru(G)
		path, pathlen = djk(src, dst)
	'''
	if get_neighbors is None:
		get_neighbors = G.get

	distance = defaultdict(lambda: INFINITY, {src: 0})
	previous = {src: None}
	queue    = [(0, src)]
	visited  = set()

	while queue:
		dist, node = heapq.heappop(queue)

		if node == dst:
			path = []

			while node is not None:
				path.append(node)
				node = previous[node]

			return tuple(reversed(path)), dist

		if node not in visited:
			visited.add(node)
			neighbors = get_neighbors(node)

			if not neighbors:
				continue

			for neighbor, weight in filter(lambda n: n[0] not in visited, neighbors):
				new_dist = dist + weight

				if new_dist < distance[neighbor]:
					distance[neighbor] = new_dist
					previous[neighbor] = node
					heapq.heappush(queue, (new_dist, neighbor))

	return (), INFINITY

def dijkstra_path_lru(G: WeightedGraphDict,
		get_neighbors: Optional[GraphNeighborsFunc]=None) \
		-> Callable[[Any,Any],Tuple[Tuple[Any],Distance]]:
	'''
	Memoized version of dijkstra_path():
		djk = dijkstra_path_lru(G)
		path, pathlen = djk(src, dst)
	'''
	@lru_cache(MAX_CACHE_SIZE)
	def wrapper(src: Any, dst: Any) -> Tuple[Tuple[Any],Distance]:
		nonlocal G, get_neighbors
		return dijkstra_path(G, src, dst, get_neighbors)
	return wrapper

def dijkstra_all(G: WeightedGraphDict, src: Any,
		get_neighbors: Optional[GraphNeighborsFunc]=None) \
		-> DefaultDict[Any,Distance]:
	'''Find the length of all the shortest paths from src to any reachable node
	in G using Dijkstra's algorithm.

	G is a weighted "graph dictionary" of the form {src: [(dst, weight)]}
	get_neighbors(node) is called to determine node neighbors (default is G.get)

	Reurns a defaultdict {node: distance}, where unreachable nodes have
	distance=INFINITY.
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

def dijkstra_all_paths(G: WeightedGraphDict, src: Any,
		get_neighbors: Optional[GraphNeighborsFunc]=None) \
		-> DefaultDict[Any,Tuple[Tuple[Any],Distance]]:
	'''Find all the shortest paths from src to any reachable node in G and their
	using Dijkstra's algorithm.

	G is a "graph dictionary" of the form {src: [(dst, weight)]}
	get_neighbors(node) is called to determine node neighbors (default is G.get)

	Returns a defaultdict {node: (path, length)}, where unreachable nodes have
	path=() and length=INFINITY. NOTE that src is always present in the result
	with path=(src,) and length=0.
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

def bellman_ford(G: WeightedGraphDict, src: Any) \
		-> Tuple[
			DefaultDict[Any,Distance],
			DefaultDict[Any,Distance],
			Callable[[Any],Deque[Any]]
		]:
	'''Find all the shortest paths from src to any reachable node in G and their
	lengths using the Bellman-Ford algorithm. IMPORTANT: all nodes of the graph
	should be in G as keys!

	G is a weighted "graph dictionary" of the form {src: [(dst, weight)]}.

	Returns a tuple (distance, previous, path_to) where distance and previous
	are two defaultdict, while path_to is a function.

	distance[node]:
		length of the shortest path from src to node
		default to INFINITY for unreachable nodes

	previous[node]:
		previous node in the shortest path from src to node
		default to None for unreachable nodes

	path_to(dst):
		convenience function which computes and returns the shortest path from
		src (fixed) to dst as a deque of nodes using the values in previous
	'''
	distance = defaultdict(lambda: INFINITY, {src: 0})
	previous = defaultdict(lambda: None)

	def path_to(dst: Any) -> Deque[Any]:
		nonlocal previous
		res = deque([])

		if previous[dst] is None:
			return res

		while previous[dst] is not None:
			res.appendleft(dst)
			dst = previous[dst]

		res.appendleft(src)
		return res

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

	return distance, previous, path_to

def floyd_warshall(G: WeightedGraphDict) \
		-> Tuple[
			DefaultDict[Any,DefaultDict[Any,Distance]],
			DefaultDict[Any,DefaultDict[Any,Distance]],
			Callable[[Any,Any],List[Any]]
		]:
	'''Find the length of the shortest paths between any pair of nodes in G and
	using the Floyd-Warshall algorithm.

	G is a weighted "graph dictionary" of the form {src: [(dst, weight)]}.

	Returns a tuple (distance, successor, path), where distance and successor
	are two defaultdict of defaultdicts, while path is a function.

	distance[a][b]:
		length of the shortest path from a to b
		default to INFINITY if b is not reachable from a

	successor[a][b]:
		next node in the shortest path from a to b
		default to None if b is not reachable from a

	path(a, b):
		convenience function which computes and returns the shortest path from
		a to b as a list of nodes using the values in successor
	'''
	distance  = defaultdict(lambda: defaultdict(lambda: INFINITY))
	successor = defaultdict(lambda: defaultdict(lambda: None))

	def path(src: Any, dst: Any) -> List[Any]:
		nonlocal successor

		if successor[src][dst] is None:
			return []

		res = [src]
		while src != dst:
			src = successor[src][dst]
			res.append(src)

		return res

	for a, bs in G.items():
		distance[a][a], successor[a][a] = 0, a

		for b, w in bs:
			distance[a][b], successor[a][b] = w, b
			distance[b][b], successor[b][b] = 0, b

	nodes = distance.keys()

	for a, b, c in product(nodes, nodes, nodes):
		bc, ba, ac = distance[b][c], distance[b][a], distance[a][c]

		if ba + ac < bc:
			distance[b][c] = ba + ac
			successor[b][c] = successor[b][a]

	if any(distance[a][a] < 0 for a in nodes):
		raise Exception('Floyd-Warshall on graph containing negative-weight cycles')

	return distance, successor, path

def kruskal(G: WeightedGraphDict) -> WeightedGraphDict:
	'''Find the minimum spanning tree (or forest) of the *undirected* graph G
	using Kruskal's algorithm.

	G is a weighted "graph dictionary" of the form {src: [(dst, weight)]}.

	Returns a new weighted graph dictionary representing the minimum spannign
	tree.
	'''
	mst   = defaultdict(list)
	uf    = UnionFind(G)
	edges = sorted((w, a, b) for a, n in G.items() for b, w in n)

	for w, a, b in edges:
		ub = uf.find(b)

		# Allow incomplete dict graphs where not all nodes are keys
		if ub is None:
			uf.add(b)
			# No need to re-compute b's representative as it will be different
			# from a's representative either way (uf.find(a) != None since a is
			# guaranteed to be in uf).

		if uf.find(a) != ub:
			mst[a].append((b, w))
			mst[b].append((a, w))
			uf.union(a, b)

	return mst

def _toposort_dependencies(G: GraphDict, reverse: bool, weighted: bool) \
		-> Tuple[DefaultDict[Any,int],DefaultDict[Any,int]]:
	'''Calculate forward and reverse dependencies of the nodes in the directed
	acyclic graph G.

	G is a "graph dictionary" of the form {src: [dst]} or {src: [(dst, weight)]}
	if weighted=True, in which case weights are ignored. G[src] should contain
	the nodes that depend on src (i.e., should come after src). If reverse=True,
	edges of G are considered inverted and the opposite relationship is
	considered.

	Returns two defaultdict:
		dep: maps each node to its number of dependencies (0 for root nodes)
		revdep: maps each node to a list of nodes that depend on it
	'''
	unweight = itemgetter(0) if weighted else lambda x: x

	if reverse:
		dep = defaultdict(int, {p: len(c) for p, c in G.items()})
		revdep = defaultdict(list)

		for child, parents in G.items():
			for parent in map(unweight, parents):
				revdep[parent].append(child)
				dep[parent] # make sure to have *all* nodes as keys in dep
	else:
		dep = defaultdict(int)
		revdep = defaultdict(tuple, {k: tuple(map(unweight, v)) for k, v in G.items()})

		for parent, children in G.items():
			dep[parent] # make sure to have *all* nodes as keys in dep
			for child in map(unweight, children):
				dep[child] += 1

	return dep, revdep

def toposort(G: GraphDict, reverse: bool=False, weighted: bool=False) -> List[Any]:
	'''Perform a topological sort of the directed acyclic graph G. No particular
	order is guaranteed whenever there are multiple nodes with no dependencies
	that can be chosen as next.

	G is a "graph dictionary" of the form {src: [dst]} or {src: [(dst, weight)]}
	if weighted=True, in which case weights are ignored. G[src] should contain
	the nodes that depend on src (i.e., should come after src). If reverse=True,
	edges of G are considered inverted and the opposite relationship is
	considered.

	Returns a list of nodes sorted in topological order.
	'''
	dep, revdep = _toposort_dependencies(G, reverse, weighted)
	queue = deque(n for n, d in dep.items() if d == 0)
	result = []

	while queue:
		node = queue.popleft()
		result.append(node)

		for child in revdep[node]:
			if dep[child] > 0:
				dep[child] -= 1
				if dep[child] == 0:
					queue.append(child)

	return result

def lex_toposort(G: GraphDict, reverse: bool=False, weighted: bool=False) -> List[Any]:
	'''Perform a lexicographical topological sort of the directed acyclic graph
	G. The smallest node is always chosen whenever there are multiple nodes with
	no dependencies that can be chosen as next.

	G is a "graph dictionary" of the form {src: [dst]} or {src: [(dst, weight)]}
	if weighted=True, in which case weights are ignored. G[src] should contain
	the nodes that depend on src (i.e., should come after src). If reverse=True,
	edges of G are considered inverted and the opposite relationship is
	considered.

	Returns a list of nodes sorted in lexicographical topological order.
	'''
	# Implemented with a min-heap as queue, so not the most efficient algorithm,
	# see: https://en.wikipedia.org/wiki/Lexicographic_breadth-first_search

	dep, revdep = _toposort_dependencies(G, reverse, weighted)
	queue = [n for n, d in dep.items() if d == 0]
	result = []

	heapq.heapify(queue)

	while queue:
		node = heapq.heappop(queue)
		result.append(node)

		for child in revdep[node]:
			if dep[child] > 0:
				dep[child] -= 1
				if dep[child] == 0:
					heapq.heappush(queue, child)

	return result

def bisection(fn: Callable[[IntOrFloat],IntOrFloat], y: IntOrFloat,
		lo: Optional[IntOrFloat]=None, hi: Optional[IntOrFloat]=None,
		tolerance: IntOrFloat=1e-9, upper: bool=False) -> IntOrFloat:
	'''Find a value x in the range [lo, hi] such that fn(x) == y.

	NOTE: fn(x) must be a monotinically increasing function for this to work! In
	case f(x) is monotonically decreasing, -fn(x) can be provided. In case f(x)
	is not monotonous, this method cannot possibly work.

	If y is an int, find an exact match for x such that fn(x) == y; return None
	on failure.

	If y is a float, find a lower bound for x instead (or upper bound if
	upper=True) stopping when the size of the range of values to search gets
	below tolerance; in this case, the search cannot fail. It is up to the
	caller to supply meaningful values for lo and hi.

	If not supplied, lo and hi are found through exponential search.

	```
	                 * * *
	               * |
	             *   |
	    y ------*    |
	           *     |
	         *       |
	       *         |
	    *  |         |
	       lo        hi
	```
	'''
	if type(y) not in (int, float):
		raise TypeError('y must be int or float, got {}'.format(type(y).__name__))

	if lo is not None and hi is not None and fn(lo) <= fn(hi):
		raise TypeError('fn(x) must be a monotonically increasing function, but have fn(lo) > fn(hi)')

	if lo is None:
		# Optimistic check
		if fn(0) <= y:
			lo = 0
		else:
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
			elif v < y:
				lo = x + 1
			else:
				return x

		return None

	# y is float
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

def binary_search(seq: Sequence[Any], x: Any) -> int:
	'''Find the index of x in the sorted sequence seq using binary search.
	Returns -1 if x not in seq.

	NOTE: seq must be indexable.
	'''
	# https://docs.python.org/3/library/bisect.html#searching-sorted-lists
	i = bisect_left(seq, x)
	if i != len(seq) and seq[i] == x:
		return i
	return -1

def knapsack(items: Dict[T,Tuple[Any,IntOrFloat]], weight_limit: IntOrFloat) \
		-> Tuple[IntOrFloat,List[T]]:
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
	def best(n: int, wl: IntOrFloat) -> IntOrFloat:
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
