#!/usr/bin/env python3

import advent
from utils import *
from string import ascii_lowercase as lowercase, ascii_uppercase as uppercase

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

def neigh4(r, c):
	for dr, dc in ((1, 0), (-1, 0), (0, 1), (0, -1)):
		rr, cc = (r + dr, c + dc)
		if 0 <= rr < len(grid) and 0 <= cc < len(grid[rr]):
			if grid[rr][cc] != '#':
				yield (rr, cc)

@lru_cache(maxsize=2**30)
def reachable_keys(src, mykeys):
	queue = deque([(0, src)])
	visited = set()
	foundkeys = {}

	while queue:
		dist, node = queue.popleft()

		if node not in visited:
			visited.add(node)

			if node in keys:
				k = keys[node]

				if k not in mykeys and (k not in foundkeys or foundkeys[k] > dist):
					foundkeys[k] = dist
					continue

			if node in doors and not doors[node] in mykeys:
				continue

			for neighbor in filter(lambda n: n not in visited, G[node]):
				new_dist = dist + 1
				queue.append((new_dist, neighbor))

	return foundkeys

@lru_cache(maxsize=2**30)
def search(pos, mykeys=frozenset()):
	keyz = reachable_keys(pos, mykeys) # -> {chiave: distanza}
	if not keyz:
		return 0, mykeys

	best = float('inf')
	bestkeys = {}

	for k, d in keyz.items():
		keypos = keys[k]
		subdist, subkeys = search(keypos, mykeys | {k})
		dist = d + subdist

		if dist < best:
			best = dist
			bestkeys = subkeys

	return best, mykeys | bestkeys

G = {}
keys = {}
doors = {}
mypos = None

for r, row in enumerate(grid):
	for c, cell in enumerate(row):
		pos = (r, c)
		if cell != '#':
			if pos not in G:
				G[pos] = set()

			for n in neigh4(*pos):
				G[pos].add(n)

			if cell in lowercase:
				keys[cell] = pos
				keys[pos] = cell
			elif cell in uppercase:
				doors[cell.lower()] = pos
				doors[pos] = cell.lower()
			elif cell == '@':
				mypos = pos


grid = get_char_matrix(fin)
steps, keys = search(mypos)
# print(steps)
advent.submit_answer(1, ans)



@lru_cache(maxsize=2**30)
def reachable_keys2(srcs, mykeys):
	queue = deque()
	visited = set()
	foundkeys = {}

	for src in srcs:
		queue.append((0, src, src))

	while queue:
		dist, node, owner = queue.popleft()

		if node not in visited:
			visited.add(node)

			if node in keys:
				k = keys[node]

				if k not in mykeys and (k not in foundkeys or foundkeys[k] > dist):
					foundkeys[k] = (owner, dist)
					continue

			if node in doors and not doors[node] in mykeys:
				continue

			for neighbor in filter(lambda n: n not in visited, G[node]):
				new_dist = dist + 1
				queue.append((new_dist, neighbor, owner))

	return foundkeys

@lru_cache(maxsize=2**30)
def search2(bots, mykeys=frozenset()):
	keyz = reachable_keys2(bots, mykeys)
	if not keyz:
		return 0

	best = float('inf')

	for k, (owner, d) in keyz.items():
		newbots = []

		for b in bots:
			if b == owner:
				newbots.append(keys[k])
			else:
				newbots.append(b)

		newbots = tuple(newbots)
		dist = d + search2(newbots, mykeys | {k})

		if dist < best:
			best = dist

	return best



del G[mypos]

for n in neigh4(*mypos):
	del G[n]

	for nn in neigh4(*n):
		if nn in G:
			G[nn].remove(n)

r, c = mypos
bots = (
	(r + 1, c + 1),
	(r + 1, c - 1),
	(r - 1, c + 1),
	(r - 1, c - 1),
)

# print(reachable_keys2(bots, frozenset()))

try:
	ans2 = search2(bots)
except RecursionError:
	print('fuck')

advent.submit_answer(2, ans2)
