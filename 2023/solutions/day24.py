#!/usr/bin/env python3

import sys
from itertools import combinations

def matrix_transpose(m):
	return list(map(list, zip(*m)))

def matrix_minor(m, i, j):
	return [row[:j] + row[j + 1:] for row in (m[:i] + m[i + 1:])]

def matrix_det(m):
	if len(m) == 2:
		return m[0][0] * m[1][1] - m[0][1] * m[1][0]

	determinant = 0
	for c in range(len(m)):
		determinant += ((-1)**c) * m[0][c] * matrix_det(matrix_minor(m, 0, c))

	return determinant

# Adapted from: https://stackoverflow.com/a/39881366/3889449
def matrix_inverse(m):
	determinant = matrix_det(m)
	cofactors = []

	for r in range(len(m)):
		row = []

		for c in range(len(m)):
			minor = matrix_minor(m, r, c)
			row.append(((-1)**(r + c)) * matrix_det(minor))

		cofactors.append(row)

	cofactors = matrix_transpose(cofactors)

	for r in range(len(cofactors)):
		for c in range(len(cofactors)):
			cofactors[r][c] /= determinant

	return cofactors

# Adapted from: https://stackoverflow.com/a/20677983/3889449
def intersection_2d_forward(a, va, b, vb):
	a1 = (a[0] + va[0], a[1] + va[1])
	b1 = (b[0] + vb[0], b[1] + vb[1])
	dx = (a[0] - a1[0], b[0] - b1[0])
	dy = (a[1] - a1[1], b[1] - b1[1])

	div = matrix_det((dx, dy))
	if div == 0:
		return None, None

	d = (matrix_det((a, a1)), matrix_det((b, b1)))

	x = matrix_det((d, dx)) / div
	if (x > a[0]) != (va[0] > 0) or (x > b[0]) != (vb[0] > 0):
		return None, None

	y = matrix_det((d, dy)) / div
	if (y > a[1]) != (va[1] > 0) or (y > b[1]) != (vb[1] > 0):
		return None, None

	return x, y

def vector_diff(a, b):
	return a[0] - b[0], a[1] - b[1], a[2] - b[2]

def get_equations(a, va, b, vb):
	# Return the coefficient matrix (A) and the constant terms vector (B) for
	# the 3 equations given by:
	#
	#   (p - a) X (v - va) == (p - b) X (v - vb)

	dx, dy, dz = vector_diff(a, b)
	dvx, dvy, dvz = vector_diff(va, vb)

	A = [
		[0, -dvz, dvy, 0, -dz, dy],
		[dvz, 0, -dvx, dz, 0, -dx],
		[-dvy, dvx, 0, -dy, dx, 0]
	]

	B = [
		b[1]*vb[2] - b[2]*vb[1] - (a[1]*va[2] - a[2]*va[1]),
		b[2]*vb[0] - b[0]*vb[2] - (a[2]*va[0] - a[0]*va[2]),
		b[0]*vb[1] - b[1]*vb[0] - (a[0]*va[1] - a[1]*va[0]),
	]

	return A, B

def matrix_mul(m, vec):
	res = []

	for row in m:
		res.append(sum(r * v for r, v in zip(row, vec)))

	return res

def solve(hailstones):
	(a, va), (b, vb), (c, vc) = hailstones[:3]

	# Let our 6 unknowns be: p = (x, y, z) and v = (vx, vy, vz)
	# Solve the linear system of 6 equations given by:
	#
	#   (p - a) X (v - va) == (p - b) X (v - vb)
	#   (p - a) X (v - va) == (p - c) X (v - vc)
	#
	# Where X represents the vector cross product.

	A1, B1 = get_equations(a, va, b, vb)
	A2, B2 = get_equations(a, va, c, vc)
	A = A1 + A2
	B = B1 + B2

	# Could also use fractions.Fraction to avoid rounding mistakes
	x = matrix_mul(matrix_inverse(A), B)
	return sum(map(round, x[:3]))


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1], 'r') if len(sys.argv) > 1 else sys.stdin

hailstones = []
total = 0

with fin:
	for line in fin:
		p, v = line.split('@')
		p = tuple(map(int, p.split(',')))
		v = tuple(map(int, v.split(',')))
		hailstones.append((p, v))

for a, b in combinations(hailstones, 2):
	x, y = intersection_2d_forward(*a, *b)
	if x is None:
		continue

	xok = 200000000000000 <= x <= 400000000000000
	yok = 200000000000000 <= y <= 400000000000000
	total += xok and yok

print('Part 1:', total)

answer = solve(hailstones)
print('Part 2:', answer)
