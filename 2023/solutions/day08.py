#!/usr/bin/env python3

import sys
from math import lcm
from itertools import cycle

def steps(g, node, directions, stop_early=True):
	directions_iter = enumerate(cycle(directions), 1)

	for n1, d in directions_iter:
		node = g[node][d]
		if node[-1] == 'Z':
			break

	if stop_early:
		return n1

	znode = node

	for loop_len, (n2, d) in enumerate(directions_iter, 1):
		node = g[node][d]
		if node[-1] == 'Z':
			break

	# Assumptions checked here:
	# 1) Each A-node should only reach one Z-node;
	# 2) Continuing from such node, we should loop back to it without
	#    encountering any other Z-nodes;
    # 3) The length of the loop is equal to the number of steps required to
	#    reach the Z-node from the A-node.
	assert node == znode
	assert n1 % len(directions) == n2 % len(directions)
	assert n1 == loop_len
	return loop_len


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

directions = tuple(int(d == 'R') for d in fin.readline().rstrip())
fin.readline()

g       = {l[:3]: (l[7:10], l[12:15]) for l in fin}
a_nodes = filter(lambda node: node[-1] == 'A', g)
steps1  = steps(g, 'AAA', directions, True)
steps2  = lcm(*map(lambda a: steps(g, a, directions), a_nodes))

print('Part 1:', steps1)
print('Part 2:', steps2)
