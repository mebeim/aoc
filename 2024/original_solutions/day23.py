#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 23)
DEBUG = 'debug' in map(str.lower, sys.argv)
# DEBUG = True
fin = advent.get_input() if not DEBUG else io.StringIO('''\
kh-tc
qp-kh
de-cg
ka-co
yn-aq
qp-ub
cg-tb
vc-aq
tb-ka
wh-tc
yn-cg
kh-ub
ta-co
de-co
tc-td
tb-wq
wh-td
ta-ka
td-qp
aq-cg
wq-ub
ub-vc
de-ta
wq-aq
wq-vc
wh-yn
ka-de
kh-ta
co-tc
wh-qp
tb-vc
td-yn
''')

lines = read_lines(fin)
ans1 = ans2 = 0

g = defaultdict(set)
for l in lines:
	a, b = l.split('-')
	g[a].add(b)
	g[b].add(a)

# f = open('x.dot', 'w')
# f.write('graph G {\n')
# for a, bs in g.items():
# 	for b in bs:
# 		f.write(f'  {a} -- {b};\n')
# f.write('}\n')

for a, b, c in combinations(g.keys(), 3):
	if a.startswith('t') or b.startswith('t') or c.startswith('t'):
		if a in g[b] and a in g[c] and b in g[c]:
			ans1 += 1

advent.print_answer(1, ans1)


g2 = nx.Graph()
for a, bs in g.items():
	for b in bs:
		g2.add_edge(a, b)

best = 0
bestc = None
for c in nx.find_cliques(g2):
	if len(c) > best:
		best = len(c)
		bestc = c

ans2 = ','.join(sorted(bestc))
advent.print_answer(2, ans2)
