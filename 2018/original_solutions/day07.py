#!/usr/bin/env python3

from utils import advent
from collections import defaultdict, namedtuple
from string import *

advent.setup(2018, 7)
fin = advent.get_input()

##################################################

def wtf(graph, node, q, visited):
	global lol

	visited.add(node)
	# print('visited', node)

	lol += node

	for n in graph[node].next:
		q.add(n)

	while len(q):
		for n in sorted(q):
			# print('tryng', n)
			if all(x in visited for x in graph[n].need):
				# print('  need satisfied, can visit', n)

				if n not in q:
					# print('  not in queue!')
					break

				q.remove(n)
				wtf(graph, n, q, visited)

def wtf2(graph, queue, done):
	totaltime = 0

	while any(w.job for w in workers):
		t = 999
		for w in workers:
			if w.job:
				t = min(t, w.left)

		assert t != 999

		# print('advancing', t, 'secs')

		totaltime += t

		for w in workers:
			if w.job:
				w.left -= t

		# print('-'*30, queue)
		# print('-'*30, workers)

		# print('checking completed jobs')

		for w in workers:
			if w.left == 0:
				if w.job:
					# print('  job', w.job, 'done')
					done.add(w.job)

					for n in graph[w.job].next:
						# print('    can', n, 'be done? ', end='')
						if all(x in done for x in graph[n].need):
							# print('yes')
							queue.add(n)
						# else:
							# print('no')

					w.job = ''

		# print('assigning new jobs')

		for w in workers:
			if not w.job and len(queue):
				w.job = min(queue)
				w.left = times[w.job]
				queue.remove(w.job)

		# print('-'*30, queue)
		# print('-'*30, workers)

	# print('work is over!')
	return totaltime

strings = list(map(str.rstrip, fin))

E = namedtuple('E', ['next', 'need'])
graph = defaultdict(lambda: E(set(), set()))

for s in strings:
	ss = s.split()
	graph[ss[1]].next.add(ss[7])
	graph[ss[7]].need.add(ss[1])

# print(graph)

roots = []
for c in graph:
	if all(c not in v.next for v in graph.values()):
		roots.append(c)

print('roots:', roots)

roots.sort()
lol = ''

wtf(graph, roots[0], set(roots[1:]), set())

advent.submit_answer(1, lol)

############

time = {}
for c in ascii_uppercase:
	time[c] = ord(c) - ord('A') + 61

class W:
	def __init__(self):
		self.left = 0
		self.job = ''
	def __repr__(self):
		if not self.job:
			return 'W(-)'
		return 'W({}, {})'.format(self.job, self.left)

workers = [W(), W(), W(), W(), W()]

times = {}
for c in graph:
	times[c] = ord(c) - ord('A') + 61


roots = set(roots)

for w in workers:
	if len(roots):
		w.job = min(roots)
		w.left = times[w.job]
		roots.remove(w.job)

# print('-'*30, workers)

ans2 = wtf2(graph, roots, set())

# 234 too low
# 1134 too high
advent.submit_answer(2, ans2)
