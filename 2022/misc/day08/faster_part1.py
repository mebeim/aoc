#!/usr/bin/env python3
#
# Faster part 1 algorithm scanning the entire grid only 4 times (once per
# direction), thus achieving a computational complexity of O(n^2) operations.
#

with open('input.txt', 'rb') as fin:
	grid = fin.read().splitlines()

height, width = len(grid), len(grid[0])
maxr, maxc = height - 1, width - 1
visible = set()

for r in range(height):
	tallest = -1
	# West to East
	for c in range(width):
		tree = grid[r][c]

		if tree > tallest:
			tallest = tree
			visible.add((r, c))

	tallest = -1
	# East to West
	for c in range(maxr, -1, -1):
		tree = grid[r][c]

		if tree > tallest:
			tallest = tree
			visible.add((r, c))

for c in range(width):
	tallest = -1
	# North to South
	for r in range(height):
		tree = grid[r][c]

		if tree > tallest:
			tallest = tree
			visible.add((r, c))

	tallest = -1
	# South to North
	for r in range(maxc, -1, -1):
		tree = grid[r][c]

		if tree > tallest:
			tallest = tree
			visible.add((r, c))

n_visible = len(visible)
print('Part 1:', n_visible)


best = 0

for r in range(1, maxr):
	row = grid[r]

	for c in range(1, maxc):
		tree = row[c]

		for e in range(c + 1, width):
			if row[e] >= tree:
				break

		for w in range(c - 1, -1, -1):
			if row[w] >= tree:
				break

		for s in range(r + 1, height):
			if grid[s][c] >= tree:
				break

		for n in range(r - 1, -1, -1):
			if grid[n][c] >= tree:
				break

		score = (e - c) * (c - w) * (s - r) * (r - n)

		if score > best:
			best = score

print('Part 2:', best)
