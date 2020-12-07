#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 7)
fin = advent.get_input()

# fin = io.StringIO('''\
# shiny gold bags contain 2 dark red bags.
# dark red bags contain 2 dark orange bags.
# dark orange bags contain 2 dark yellow bags.
# dark yellow bags contain 2 dark green bags.
# dark green bags contain 2 dark blue bags.
# dark blue bags contain 2 dark violet bags.
# dark violet bags contain no other bags.
# ''')

# eprint(*fin, sep=''); fin.seek(0, 0)
timer_start()

lines = get_lines(fin)
G = defaultdict(list)

for line in lines:
	l, r = line.strip().split('bags contain')
	l = l.strip()
	r = r.strip()

	for rr in r.split(', '):
		rr = rr.replace('bags', '').replace('bag', '').replace('.', '').strip()
		if rr.startswith('no'):
			continue
		else:
			i = rr.find(' ')
			n = int(rr[:i])
			rr = rr[i+1:]

		G[l].append((rr, n))

djk = dijkstra_lru(G)

ans = 0
seen = set()
for k in G:
	if k == 'shiny gold':
		continue

	if k not in seen:
		seen.add(k)

		if djk(k, 'shiny gold') != INFINITY:
			ans += 1

advent.print_answer(1, ans)

def xplore(src):
	res = 0

	if src in G:
		for n, wg in G[src]:
			res += wg
			res += wg * xplore(n)

	return res

# dump_dict(G)

ans2 = xplore('shiny gold')

# 32589 wrong
advent.print_answer(2, ans2)
