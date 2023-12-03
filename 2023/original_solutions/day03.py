#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 3)
fin = advent.get_input()
grid = read_char_matrix(fin)

ans = 0
notsymbols = set('0123456789.')
adj_to = defaultdict(list)

for r, row in enumerate(grid):
	number = ''
	lastc = -1

	c = 0
	while c < len(row):
		while c < len(row) and not row[c].isdigit():
			c += 1

		if c >= len(row):
			break

		start = c
		end = c
		ok = False
		adj_symbols = set()

		while c < len(row) and row[c].isdigit():
			for nr, nc in neighbors8(grid, r, c):
				n = grid[nr][nc]
				if n not in notsymbols:
					ok = True
					ident = (nr, nc, n)
					adj_symbols.add(ident)

			end += 1
			c += 1

		if ok:
			num = int(''.join(row[start:end]))
			ans += num

			for ident in adj_symbols:
				adj_to[ident].append(num)

advent.print_answer(1, ans)


ans = 0
for k, v in adj_to.items():
	if len(v) == 2:
		ans += prod(v)

advent.print_answer(2, ans)
