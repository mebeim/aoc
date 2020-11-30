#!/usr/bin/env python3

from utils import advent

import sys
import networkx as nx
import matplotlib.pyplot as plt
from collections import deque

def log(s, *a):
	sys.stderr.write(s.format(*a))
	sys.stderr.flush()

def reclog(depth):
	def fn(s, *a):
		log(' |'*depth + ' ' + s, *a)
	return fn

advent.setup(2018, 20)
fin = advent.get_input()
# print(*fin)

##################################################

def dump_graph(G):
	lol = nx.spring_layout(G)
	nx.draw(G, lol, with_labels=True)
	# edge_labels = nx.get_edge_attributes(G, 'path')
	# nx.draw_networkx_edge_labels(G, lol, edge_labels)
	nx.draw_networkx_edge_labels(G, lol)
	plt.show()

def build_graph(s):
	g     = nx.Graph()
	q     = deque()
	head  = (0, 0)

	g.add_node(head)

	i = 0
	l = len(s)

	for c in s:
		i += 1
		log('Building graph: {}/{}\r', i, l)

		if c == '(':
			q.append(head)
		elif c == '|':
			head = q[-1]
		elif c == ')':
			q.pop()
		else:
			newhead = (head[0] + deltas[c][0], head[1] + deltas[c][1])
			g.add_edge(head, newhead)
			head = newhead

	log('\n')

	return g

deltas = {
	'N': ( 0,  1),
	'S': ( 0, -1),
	'E': ( 1,  0),
	'W': (-1,  0)
}

directions = fin.read().strip()[1:-1]
graph = build_graph(directions)

paths = nx.single_source_dijkstra_path_length(graph, (0, 0))
ans = max(paths.values())


# dump_graph(graph)

advent.submit_answer(1, ans)

tot = 0
for p in  paths.values():
	if p >= 1000:
		tot += 1

ans2 = tot

advent.submit_answer(2, ans2)
