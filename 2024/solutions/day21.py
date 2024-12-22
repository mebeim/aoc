#!/usr/bin/env python3

import sys
from collections import defaultdict, deque
from math import inf as INFINITY


def bfs_all_paths(g, src, dst, cache={}):
	k = src, dst
	if k in cache:
		return cache[k]

	q = deque([(src, '')])
	distance = defaultdict(lambda: INFINITY, {src: 0})
	paths = []

	while q:
		node, path = q.popleft()
		if node == dst:
			paths.append(path)
			continue

		for neighbor, direction in g[node]:
			d = distance[node] + 1
			if d > distance[dst] or d > distance[neighbor]:
				continue

			distance[neighbor] = d
			q.append((neighbor, path + direction))

	cache[k] = paths
	return paths


def solve(pad, code, robot, cur='A', cache={}):
	k = code, robot, cur
	if k in cache:
		return cache[k]

	if not code:
		cache[k] = 0
		return 0

	nxt = code[0]
	paths = bfs_all_paths(pad, cur, nxt)

	if robot == 0:
		# "Root" dirpad operated by first robot: the number of buttons the human
		# will have to press equals the length of the shortest path passing
		# through all chars of the code
		best = len(paths[0]) + 1
	else:
		# Non-root pad: find the optimal path based on how many steps it takes
		# for the parent robot to direct this one
		best = min(solve(dirpad, p + 'A', robot - 1) for p in paths)

	res = cache[k] = best + solve(pad, code[1:], robot, nxt)
	return res


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

# +---+---+---+
# | 7 | 8 | 9 |
# +---+---+---+
# | 4 | 5 | 6 |
# +---+---+---+
# | 1 | 2 | 3 |
# +---+---+---+
#     | 0 | A |
#     +---+---+
numpad = {
	'A': ('0<', '3^'),
	'0': ('A>', '2^'),
	'1': ('2>', '4^'),
	'2': ('0v', '1<', '3>', '5^'),
	'3': ('Av', '2<', '6^'),
	'4': ('1v', '5>', '7^'),
	'5': ('2v', '4<', '6>', '8^'),
	'6': ('3v', '5<', '9^'),
	'7': ('4v', '8>'),
	'8': ('5v', '7<', '9>'),
	'9': ('6v', '8<'),
}

#     +---+---+
#     | ^ | A |
# +---+---+---+
# | < | v | > |
# +---+---+---+
dirpad = {
	'A': ('>v', '^<'),
	'^': ('A>', 'vv'),
	'<': ('v>',),
	'>': ('v<', 'A^'),
	'v': ('<<', '>>', '^^'),
}

total1 = total2 = 0
for code in fin.read().splitlines():
	num = int(code[:-1])
	total1 += num * solve(numpad, code, 2)
	total2 += num * solve(numpad, code, 25)

print('Part 1:', total1)
print('Part 2:', total2)
