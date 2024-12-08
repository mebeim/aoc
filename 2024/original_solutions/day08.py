#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 8)
fin = advent.get_input()

grid = read_char_matrix(fin)
antennas = []

for r, row in enumerate(grid):
	for c, char in enumerate(row):
		if char != '.':
			antennas.append((r, c, char))

points = set()

for a, b in product(antennas, repeat=2):
	if a == b:
		continue

	r1, c1, p1 = a
	r2, c2, p2 = b
	if p1 != p2:
		continue

	dr = r2 - r1
	dc = c2 - c1

	s = z3.Solver()
	r = z3.Int('r')
	c = z3.Int('c')
	s.add(r == r1 + 2 * dr)
	s.add(r == r2 + dr)
	s.add(c == c1 + 2 * dc)
	s.add(c == c2 + dc)
	if s.check() == z3.sat:
		m = s.model()
		points.add((m.eval(r).as_long(), m.eval(c).as_long()))

	s = z3.Solver()
	r = z3.Int('r')
	c = z3.Int('c')
	s.add(r == r1 - dr)
	s.add(r == r2 - 2 * dr)
	s.add(c == c1 - dc)
	s.add(c == c2 - 2 * dc)
	if s.check() == z3.sat:
		m = s.model()
		points.add((m.eval(r).as_long(), m.eval(c).as_long()))

points = list(filter(lambda p: 0 <= p[0] < len(grid) and 0 <= p[1] < len(grid[0]), points))
ans1 = len(points)
advent.print_answer(1, ans1)


points = set()

for a, b in product(antennas, repeat=2):
	if a == b:
		continue

	r1, c1, p1 = a
	r2, c2, p2 = b
	if p1 != p2:
		continue

	dr = r2 - r1
	dc = c2 - c1

	for m in count(0):
		r = r1 + m * dr
		c = c1 + m * dc

		if not (0 <= r < len(grid) and 0 <= c < len(grid[0])):
			break

		points.add((r, c))

points = list(filter(lambda p: 0 <= p[0] < len(grid) and 0 <= p[1] < len(grid[0]), points))
ans2 = len(points)
advent.print_answer(2, ans2)
