#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 18)
fin = advent.get_input()

lines = read_lines(fin)

grid = []
for r in range(71):
	grid.append(['.'] * 71)

for i, line in enumerate(lines):
	if i == 1024:
		break
	x,y = map(int, line.split(','))
	grid[x][y] = '#'

# dump_char_matrix(grid)

g = graph_from_grid(grid, find='.', avoid='#', coords=True, weighted=True, get_neighbors=neighbors4)
# dump_dict(g)

ans1 = dijkstra(g, (0,0,'.'), (70,70,'.'))

# p, _ = dijkstra_path(g, (0,0,'.'), (70,70,'.'))
# for x, y, _ in p:
# 	grid[x][y] = 'O'
# eprint()
# dump_char_matrix(grid)

advent.print_answer(1, ans1)


grid = []
for r in range(71):
	grid.append(['.'] * 71)

walls = set()
offset = 0

for i, line in enumerate(lines):
	x,y = map(int, line.split(','))
	grid[x][y] = '#'

	g = graph_from_grid(grid, find='.', avoid='#', coords=True, weighted=True, get_neighbors=neighbors4)
	dist = dijkstra(g, (0, 0,'.'), (70, 70, '.'))
	# eprint(x, y, dist)

	if dist == INFINITY:
		ans2 = line.strip()
		break

advent.print_answer(2, ans2)
