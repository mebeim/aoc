#!/usr/bin/env python3

from utils.all import *

def score(valves, rates):
	s = 0
	for v, t in valves:
		s += rates[v] * t
	return s

def choices(distance, rates, time=30, chosen=(('AA',0),), todo=None):
	if todo is None:
		todo = frozenset(distance) - {'AA'}

	res = [chosen]

	for nxt in todo:
		if rates[nxt] == 0:
			continue

		newtime = time - distance[chosen[-1][0]][nxt] - 1
		if newtime <= 1:
			continue

		res += choices(distance, rates, newtime, chosen + ((nxt, newtime),), todo - {nxt})

	filtered = []
	for c in res:
		t = c[-1][1]
		if any(distance[c[-1][0]][x] < t for x in todo):
			filtered.append(c)
	res = filtered

	return res

# too many, would have been nice
# def choices2(distance, rates, time1=26, time2=26, chosen1=(('AA',0),), chosen2=(('AA',0),), todo=None):
# 	if todo is None:
# 		todo = frozenset(distance) - {'AA'}

# 	res1, res2 = [], []

# 	for nxt in todo:
# 		if rates[nxt] == 0:
# 			continue

# 		# give to 1
# 		newtime = time1 - distance[chosen1[-1][0]][nxt] - 1
# 		if newtime <= 1:
# 			continue

# 		res1 += choices2(distance, rates, newtime, time2, chosen1 + ((nxt, newtime),), chosen2, todo - {nxt})

# 		# give to 2
# 		newtime = time2 - distance[chosen2[-1][0]][nxt] - 1
# 		if newtime <= 1:
# 			continue

# 		res2 += choices2(distance, rates, time1, newtime, chosen1, chosen2 + ((nxt, newtime),), todo - {nxt})

# 	return res1, res2


advent.setup(2022, 16)
DEBUG = 'debug' in map(str.lower, sys.argv)
fin = advent.get_input() if not DEBUG else io.StringIO('''\
Valve AA has flow rate=0; tunnels lead to valves DD, II, BB
Valve BB has flow rate=13; tunnels lead to valves CC, AA
Valve CC has flow rate=2; tunnels lead to valves DD, BB
Valve DD has flow rate=20; tunnels lead to valves CC, AA, EE
Valve EE has flow rate=3; tunnels lead to valves FF, DD
Valve FF has flow rate=0; tunnels lead to valves EE, GG
Valve GG has flow rate=0; tunnels lead to valves FF, HH
Valve HH has flow rate=22; tunnel leads to valve GG
Valve II has flow rate=0; tunnels lead to valves AA, JJ
Valve JJ has flow rate=21; tunnel leads to valve II

# Valve AA has flow rate=0; tunnels lead to valves BB
# Valve BB has flow rate=13; tunnels lead to valves AA, CC
# Valve CC has flow rate=2; tunnels lead to valves BB
''')

lines = read_lines(fin)
timer_start()

g = defaultdict(list)
rates = {}

for line in lines:
	line = line.strip()
	if not line or line.startswith('#'):
		continue

	l = line.split()
	a = l[1]
	bs = list(map(lambda x: x.rstrip(','), l[9:]))
	r = int(l[4][len('rate='):-1])
	rates[a] = r

	for b in bs:
		g[a].append((b, 1))

distance, successor, path = floyd_warshall(g)

cc = choices(distance, rates)
# eprint(len(cc)) # 214228

best = 0
for c in cc:
	# eprint(c)
	s = score(c, rates)
	if s > best:
		best = s

advent.print_answer(1, best)



import resource
resource.setrlimit(resource.RLIMIT_AS, (10 * 2**30,) * 2) # 10G

# too many
# eprint(len(choices2(distance, rates)))

cc = choices(distance, rates, 26)
# eprint(len(cc)) # 54176

maxscore = defaultdict(int)

for c in cc:
	k = frozenset(map(itemgetter(0), c[1:]))
	s = score(c, rates)

	if s > maxscore[k]:
		maxscore[k] = s

best = 0
for a, sa in maxscore.items():
	for b, sb in maxscore.items():
		if a & b:
			continue

		s = sa + sb
		if s > best:
			best = s

advent.print_answer(2, best)
