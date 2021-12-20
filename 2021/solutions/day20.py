#!/usr/bin/env python3

from utils import advent

def enhance_once(img, rules, outside_on):
	minr, maxr = min(r for r, _ in img), max(r for r, _ in img)
	minc, maxc = min(c for _, c in img), max(c for _, c in img)
	new = set()

	for row in range(minr - 1, maxr + 2):
		for col in range(minc - 1, maxc + 2):
			idx = 0

			for r in (row - 1, row, row + 1):
				for c in (col - 1, col, col + 1):
					idx <<= 1
					idx |= ((r, c) in img)
					idx |= outside_on and (r < minr or r > maxr or c < minc or c > maxc)

			if rules[idx]:
				new.add((row, col))

	return new

def enhance(img, rules, steps):
	for i in range(steps):
		img = enhance_once(img, rules, rules[0] and i % 2 == 1)
	return img


advent.setup(2021, 20)
fin = advent.get_input()


rules = tuple(x == '#' for x in next(fin).rstrip())
assert not (rules[0] and rules[-1]), 'Invalid rules!'

next(fin)
img = set()

for r, row in enumerate(fin):
	for c, char in enumerate(row):
		if char == '#':
			img.add((r, c))


img = enhance(img, rules, 2)
ans = len(img)
advent.print_answer(1, ans)


img = enhance(img, rules, 48)
ans = len(img)
advent.print_answer(2, ans)
