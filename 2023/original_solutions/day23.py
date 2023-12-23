#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 23)
DEBUG = 'debug' in map(str.lower, sys.argv)
fin = advent.get_input() if not DEBUG else io.StringIO('''\
#.#####################
#.......#########...###
#######.#########.#.###
###.....#.>.>.###.#.###
###v#####.#v#.###.#.###
###.>...#.#.#.....#...#
###v###.#.#.#########.#
###...#.#.#.......#...#
#####.#.#.#######.#.###
#.....#.#.#.......#...#
#.#####.#.#.#########v#
#.#...#...#...###...>.#
#.#.#v#######v###.###v#
#...#.>.#...>.>.#.###.#
#####v#.#.###v#.#.###.#
#.....#...#...#.#.#...#
#.#########.###.#.#.###
#...###...#...#...#.###
###.###.#.###v#####v###
#...#...#.#.>.>.#.>.###
#.###.###.#.###.#.#v###
#.....###...###...#...#
#####################.#
''')

grid = read_char_matrix(fin)
timer_start()

def neighbors(grid, r, c):
	cell = grid[r][c]

	if cell == '>':
		n = [(r, c + 1)]
	elif cell == '<':
		n = [(r, c - 1)]
	elif cell == 'v':
		n = [(r + 1, c)]
	elif cell == '^':
		n = [(r - 1, c)]
	else:
		n = neighbors4_coords(r, c)

	for rr, cc in n:
		if 0 <= rr < HEIGHT and 0 <= cc < HEIGHT:
			if grid[rr][cc] != '#':
				yield rr, cc

sys.setrecursionlimit(100000)

@selective_cache('cur', 'pathlen')
def search_grid(cur, dst, pathlen, seen):
	if cur == dst:
		return pathlen, True

	okk = False
	best = 0

	for n in filter(lambda x: x not in seen, neighbors(grid, *cur)):
		new, ok = search_grid(n, dst, pathlen + 1, seen | {cur})
		if not ok:
			continue

		if new > best:
			best = new
			okk = True

	return best, okk

def is_node(grid, rc, src, dst):
	if rc == src:
		return True
	if rc == dst:
		return True

	return len(tuple(neighbors4(grid, *rc, '#'))) >= 3

def adjacent_nodes(grid, rc, src, dst):
	q = deque([(rc, 0)])
	seen = set()

	while q:
		rc, dist = q.popleft()

		assert rc not in seen
		seen.add(rc)

		for n in neighbors4(grid, *rc, '#'):
			if n in seen:
				continue

			if is_node(grid, n, src, dst):
				yield (n, dist + 1)
				continue

			q.append((n, dist + 1))

def grid_to_graph(grid, src, dst):
	g = defaultdict(list)
	q = deque([src])
	seen = set()

	while q:
		rc = q.popleft()
		if rc in seen:
			continue

		seen.add(rc)

		for n, weight in adjacent_nodes(grid, rc, src, dst):
			g[rc].append((n, weight))
			q.append(n)

	return g

def search_graph(g, cur, dst, pathlen, seen, path, cache={}):
	k = (cur, path)
	if k in cache:
		return cache[k]

	if cur == dst:
		cache[k] = (pathlen, True)
		return pathlen, True

	okk = False
	best = 0
	newseen = seen | {cur}

	for n, weight in g[cur]:
		if n in seen:
			continue

		new, ok = search_graph(g, n, dst, pathlen + weight, newseen, path + (cur,))
		if not ok:
			continue

		if new > best:
			okk = True
			best = new

	cache[k] = (best, okk)
	return best, okk


HEIGHT, WIDTH = len(grid), len(grid[0])
src = (0, 1)
dst = (HEIGHT - 1, WIDTH - 2)

ans1, ok = search_grid(src, dst, 0, frozenset())
search_grid.cache_clear()
assert ok
advent.print_answer(1, ans1)

g = grid_to_graph(grid, src, dst)
# dump_dict(g)

# for r, row in enumerate(grid):
# 	for c, cell in enumerate(row):
# 		if cell in '.<>^v':
# 			grid[r][c] = ' '

# for r, c in g:
# 	grid[r][c] = 'X'
# dump_char_matrix(grid)

ans2, ok = search_graph(g, src, dst, 0, frozenset(), ())
assert ok

# 6454 too low
advent.print_answer(2, ans2)
