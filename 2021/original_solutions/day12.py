#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 12)
if 'debug' not in map(str.lower, sys.argv):
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
start-A
start-b
A-c
A-b
b-d
A-end
b-end
''')

eprint(*fin, sep='', end='----- end of input -----\n\n'); fin.seek(0, 0)
timer_start()

ans = 0
try: ints = get_ints(fin, True); fin.seek(0, 0)
except: pass
try: lines = get_lines(fin); fin.seek(0, 0)
except: pass
try: mat = get_char_matrix(fin, rstrip=False, lstrip=False); fin.seek(0, 0)
except: pass

G = defaultdict(list)

for l in lines:
	a, b = l.split('-')
	G[a].append(b)
	G[b].append(a)

def bfs(G, src, dst):
	queue = deque([(src, (src,), {src}, 0)])

	while queue:
		node, path, seen, thresh = queue.popleft()
		if node == dst:
			yield path
			continue

		for n in G[node]:
			if n == 'start':
				continue

			if n.islower() and n in seen:
				if thresh == 0:
					queue.append((n, path + (n,), seen | {n}, thresh + 1))
				else:
					continue
			else:
				queue.append((n, path + (n,), seen | {n}, thresh))

def find(G, src, dst, path=[]):
	if src == dst:
		return [path]

	res = []
	for n in G[src]:
		if n == 'start':
			continue

		if n.islower() and n in path:
			continue

		res += find(G, n, dst, path + [n])

	return res


#     start
#     /   \
# c--A-----b--d
#     \   /
#      end


# print(G)
for p in find(G, 'start', 'end', ['start']):
	ans += 1


advent.print_answer(1, ans)

ans = 0

for p in bfs(G, 'start', 'end'):
	ans += 1


advent.print_answer(2, ans)
