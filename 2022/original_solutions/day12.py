#!/usr/bin/env python3

from utils.all import *

advent.setup(2022, 12)
DEBUG = 'debug' in map(str.lower, sys.argv)
fin = advent.get_input() if not DEBUG else io.StringIO('''\
Sabqponm
abcryxxl
accszExk
acctuvwj
abdefghi
''')

grid = read_char_matrix(fin)
g = graph_from_grid(grid, find='QWERTYUIOPASDFGHJKLZXCVBNM'.lower() + 'ES', avoid='', coords=True, get_neighbors=neighbors4)

ans = 0
for x in g:
	if 'E' in x:
		dst = x
	elif 'S' in x:
		src = x

def neigh(grid, r, c, avoid):
	a = grid[r][c]

	if a == 'S':
		yield from neighbors4(grid, r, c)
		return

	for nr, nc in neighbors4(grid, r, c):
		v = grid[nr][nc]
		if v == 'E':
			v = 'z'

		if ord(v) <= ord(a) + 1:
			yield nr, nc

ans = grid_bfs(grid, src[:2], dst[:2], get_neighbors=neigh)
advent.print_answer(1, ans)


best = float('inf')

for src in g:
	if src[2] != 'a':
		continue

	ans = grid_bfs(grid, src[:2], dst[:2], get_neighbors=neigh)
	if ans < best:
		best = ans

advent.print_answer(2, best)
