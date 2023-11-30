#!/usr/bin/env python3

import sys
from collections import deque, defaultdict

def n_paths(G, src, dst):
	stack = deque([(src, {src})])
	total = 0

	while stack:
		node, visited = stack.pop()
		if node == dst:
			total += 1
			continue

		for n in G[node]:
			if n in visited and n.islower():
				continue

			stack.append((n, visited | {n}))

	return total

def n_paths2(G, src, dst):
	stack = deque([(src, {src}, False)])
	total = 0

	while stack:
		node, visited, double = stack.pop()
		if node == dst:
			total += 1
			continue

		for n in G[node]:
			if n not in visited or n.isupper():
				stack.append((n, visited | {n}, double))
				continue

			if double:
				continue

			stack.append((n, visited, True))

	return total


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

G = defaultdict(list)

for edge in fin:
	a, b = edge.rstrip().split('-')

	if b != 'start':
		G[a].append(b)
	if a != 'start':
		G[b].append(a)

n1 = n_paths(G, 'start', 'end')
n2 = n_paths2(G, 'start', 'end')

print('Part 1:', n1)
print('Part 2:', n2)
