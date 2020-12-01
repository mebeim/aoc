#!/usr/bin/env python3

from utils import advent
import copy
import heapq
from collections import defaultdict

def lex_toposort(graph, queue):
	# Could easily be done using networkx.
	# Implemented just for fun and educational purposes.
	res = ''

	while queue:
		cur = heapq.heappop(queue)
		res += cur

		for n in graph[cur][1]:
			graph[n][0] -= 1

			if graph[n][0] == 0:
				heapq.heappush(queue, n)

	return res

def work(graph, queue, duration, max_workers):
	total_time = 0
	workers = []
	done = set()

	while workers or queue:
		while queue and len(workers) < max_workers:
			job = heapq.heappop(queue)
			heapq.heappush(workers, [duration[job], job])

		t = workers[0][0]
		total_time += t

		for w in workers:
			w[0] -= t

		while workers and workers[0][0] == 0:
			job = heapq.heappop(workers)[1]
			done.add(job)

			for n in graph[job][1]:
				graph[n][0] -= 1

				if graph[n][0] == 0:
					heapq.heappush(queue, n)

	return total_time


advent.setup(2018, 7)
fin = advent.get_input()

graph = defaultdict(lambda: [0, set()])

for line in fin:
	s = line.split()
	graph[s[1]][1].add(s[7])
	graph[s[7]][1].add(s[1])
	graph[s[7]][0] += 1

roots = []
for letter, node in graph.items():
	if node[0] == 0:
		heapq.heappush(roots, letter)

order = lex_toposort(copy.deepcopy(graph), roots[:])
advent.print_answer(1, order)


durations = {}
for c in graph:
	durations[c] = ord(c) - ord('A') + 61

total = work(graph, roots, durations, 5)
advent.print_answer(2, total)
