#!/usr/bin/env python3

with open('input.txt') as fin:
	A, B = map(int, fin)

x = 1
v = 7

while v != A and v != B:
	v = (v * 7) % 20201227
	x += 1


key = pow(B if v == A else A, x, 20201227)
print('Part 1:', key)
