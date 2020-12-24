#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 24)
fin = advent.get_input()
TESTPLZ = any(a.lower() == 'test' for a in sys.argv[1:])
ftest = io.StringIO('''\
sesenwnenenewseeswwswswwnenewsewsw
neeenesenwnwwswnenewnwwsewnenwseswesw
seswneswswsenwwnwse
nwnwneseeswswnenewneswwnewseswneseene
swweswneswnenwsewnwneneseenw
eesenwseswswnenwswnwnwsewwnwsene
sewnenenenesenwsewnenwwwse
wenwwweseeeweswwwnwwe
wsweesenenewnwwnwsenewsenwwsesesenwne
neeswseenwwswnwswswnw
nenwswwsewswnenenewsenwsenwnesesenew
enewnwewneswsewnwswenweswnenwsenwsw
sweneswneswneneenwnewenewwneswswnese
swwesenesewenwneswnwwneseswwne
enesenwswwswneneswsenwnewswseenwsese
wnwnesenesenenwwnenwsewesewsesesew
nenewswnwewswnenesenwnesewesw
eneswnwswnwsenenwnwnwwseeswneewsenese
neswnwewnwnwseenwseesewsenwsweewe
wseweeenwnesenwwwswnew
''')

if TESTPLZ:
	fin = ftest

timer_start()

lines = get_lines(fin)
# e, se, sw, w, nw, and ne

def move(moves):
	x, y = 0, 0

	while moves:
		if moves.startswith('e'):
			x += 1
			moves = moves[1:]
		elif moves.startswith('se'):
			x += 1
			y += 1
			moves = moves[2:]
		elif moves.startswith('sw'):
			y += 1
			moves = moves[2:]
		elif moves.startswith('w'):
			x -= 1
			moves = moves[1:]
		elif moves.startswith('nw'):
			x -= 1
			y -= 1
			moves = moves[2:]
		elif moves.startswith('ne'):
			y -= 1
			moves = moves[2:]

	return x, y

def neigh(g, x, y):
	deltas = ((1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1))

	tot = 0
	for dx, dy in deltas:
		p = (x + dx, y + dy)
		if p in g:
			tot += 1 if g[p] else 0
	return tot

def expand(g):
	deltas = ((1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1))
	kk = list(g.keys())

	for x, y in kk:
		for dx, dy in deltas:
			p = (x + dx, y + dy)
			g[p]

def evolve(g):
	old = deepcopy(g)
	expand(g)

	for p in g:
		tile = old[p]
		nblack = neigh(old, *p)

		if tile and (nblack == 0 or nblack > 2):
			g[p] = False
		elif not tile and (nblack == 2):
			g[p] = True

	return g


G = defaultdict(lambda: False)
# True = black up

for l in lines:
	p = move(l.strip())
	G[p] = not G[p]

ans = sum(G.values())

# 225 wrong
advent.print_answer(1, ans)


for _ in range(100):
	G = evolve(G)

ans2 = sum(G.values())

# 100 wrong
advent.print_answer(2, ans2)
