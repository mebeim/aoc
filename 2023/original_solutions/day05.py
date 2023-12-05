#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 5)
fin = advent.get_input()

ans = 0
data = fin.read().split('\n\n')
seeds = extract_ints(data[0])
steps = []

for x in data[1:]:
	ints = extract_ints(x)
	steps.append([ints[i:i + 3] for i in range(0, len(ints), 3)])

ans = INFINITY

for s in seeds:
	for step in steps:
		for dst, src, sz in step:
			src_end = src + sz - 1

			if src <= s <= src_end:
				s = s - src + dst
				break

	ans = min(ans, s)

advent.print_answer(1, ans)


def overlap(a, b, c, d):
	return not (a > d or b < c)

ss = [seeds[i:i+2] for i in range(0, len(seeds), 2)]
cur = [(a, a + b - 1) for a, b in ss]
cur = deque(cur)

for step in steps:
	new = deque()

	while cur:
		a, b = cur.popleft()

		for dst, src, sz in step:
			c, d = src, src + sz - 1
			delta = dst - src

			if not overlap(a, b, c, d):
				continue

			# C---a---b---D completely inside
			#     xxxxx
			if c <= a <= d and c <= b <= d:
				new.append((a + delta, b + delta))
				break

			# a---C---b---D escapes left
			#     xxxxx
			if c <= b <= d:
				# C---b (overlap)
				new.append((c + delta, b + delta))
				# a---C (no overlap)
				cur.append((a, c - 1))
				break

			# C---a---D---b escapes right
			# xxxxx
			if c <= a <= d:
				# C---a (overlap)
				new.append((a + delta, d + delta))
				# D---b (no overlap)
				cur.append((d + 1, b))
				break

			# a---C---D---b escapes both sides
			#     xxxxx
			if a < c and b > d:
				# C---D (overlap)
				new.append((c + delta, d + delta))
				# a---C (no overlap)
				# D---b (no overlap)
				cur.extend(((d + 1, b), (a, c - 1)))
				break
		else:
			# no overlap with any segment
			new.append((a, b))

	cur = new

ans = min(map(itemgetter(0), cur))
advent.print_answer(2, ans)
