#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 21)
fin = advent.get_input()

lines = read_lines(fin)
ans1 = ans2 = 0

# +---+---+---+
# | 7 | 8 | 9 |
# +---+---+---+
# | 4 | 5 | 6 |
# +---+---+---+
# | 1 | 2 | 3 |
# +---+---+---+
#     | 0 | A |
#     +---+---+

class D(dict):
	pass

gnums = D({
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
})
gnums.name = 'gnums'

#     +---+---+
#     | ^ | A |
# +---+---+---+
# | < | v | > |
# +---+---+---+

gdirs = D({
	'A': ('>v', '^<'),
	'^': ('A>', 'vv'),
	'<': ('v>',),
	'>': ('v<', 'A^'),
	'v': ('<<', '>>', '^^'),
})
gdirs.name = 'gdirs'


@selective_cache('src', 'dst')
def bfs_all_paths(g, src, dst):
	queue = deque([(src, '')])
	distance = defaultdict(lambda: INFINITY, {src: 0})
	paths = []

	while queue:
		node, path = queue.popleft()
		if node == dst:
			if len(path) <= distance[dst]:
				paths.append(path)
			continue

		for neighbor, key in g[node]:
			d = distance[node] + 1
			if d > distance[dst] or d > distance[neighbor]:
				continue

			distance[neighbor] = d
			queue.append((neighbor, path + key))

	assert len(set(map(len, paths))) == 1
	return paths


@cache
# @log_calls_recursive()
def solve(graph_name, code, robot, curchar='A'):
	g = gdirs if graph_name == 'gdirs' else gnums
	if not code:
		return 0

	if robot == 0:
		# Just follow any path as is
		res = 0
		for a, b in sliding_window(curchar + code, 2):
			res += len(bfs_all_paths(g, a, b)[0]) + 1
		return res

	# Check all possible paths I can use to get from curchar to nextchar
	nextchar = code[0]
	paths = bfs_all_paths(g, curchar, nextchar)
	# solve.eprint(f'{curchar=} {nextchar=} {paths=}')

	best = INFINITY
	for path in paths:
		x = solve('gdirs', path + 'A', robot - 1)
		if x < best:
			best = x

	return best + solve(g.name, code[1:], robot, nextchar)


for code in lines:
	s = solve('gnums', code, 2)
	ans1 += s * int(code[:-1])

advent.print_answer(1, ans1)


for code in lines:
	s = solve('gnums', code, 25)
	ans2 += s * int(code[:-1])

advent.print_answer(2, ans2)
