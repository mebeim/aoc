#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 15)
DEBUG = 'debug' not in map(str.lower, sys.argv)
if DEBUG:
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
1163751742
1381373672
2136511328
3694931569
7463417111
1319128137
1359912421
3125421639
1293138521
2311944581
''')

# eprint(*fin, sep='', end='----- end of input -----\n\n'); fin.seek(0, 0)
timer_start()

try: mat = get_char_matrix(fin, rstrip=False, lstrip=False); fin.seek(0, 0)
except: pass

ans = 0
G = defaultdict(list)

grid = [[int(x) for x in row] for row in mat]

for r, row in enumerate(grid):
	for c, cell in enumerate(row):
		for nr, nc in neighbors4(grid, r, c):
			G[r, c].append(((nr, nc), grid[nr][nc]))
			G[nr, nc].append(((r, c), grid[r][c]))

# dump_dict(G)

start = (0,0)
end = (len(grid)-1, len(grid[0])-1)

ans = dijkstra(G, start, end)


advent.print_answer(1, ans)
# wait('Submit? ')
# advent.submit_answer(1, ans)


new = deepcopy(grid)
R, C = len(new), len(new[0])

for _ in range(4):
	tmp = [[(x + 1 if x < 9 else 1) for x in row] for row in grid]

	for r in range(R):
		new[r].extend(tmp[r])

	grid = deepcopy(tmp)

old = deepcopy(new)

for _ in range(4):
	tmp = [[(x + 1 if x < 9 else 1) for x in row] for row in old]
	new.extend(tmp)
	old = deepcopy(tmp)

# ... there is no such thing as too many deepcopy()! LOL

for row in new:
	x = ''.join(map(str,row))
	# eprint(x)

start = (0,0)
end = (len(new)-1, len(new[0])-1)
G = defaultdict(list)
for r, row in enumerate(new):
	for c, cell in enumerate(row):
		for nr, nc in neighbors4(new, r, c):
			G[r, c].append(((nr, nc), new[nr][nc]))
			G[nr, nc].append(((r, c), new[r][c]))

# eprint(end)
ans = dijkstra(G, start, end)

advent.print_answer(2, ans)
# wait('Submit? ')
# advent.submit_answer(2, ans)
