#!/usr/bin/env python3

import sys
from collections import deque
from operator import itemgetter

def parse_input(fin):
	sections = fin.read().split('\n\n')
	seeds    = sections[0]
	seeds    = list(map(int, seeds[6:].split()))
	mappings = []

	for section in sections[1:]:
		mapping = []
		mappings.append(mapping)

		for line in section.splitlines()[1:]:
			dst, src, length = map(int, line.split())
			mapping.append((src, src + length, dst - src))

	return seeds, mappings

def solve(segments, mappings):
	for mapping in mappings:
		processed = deque()

		while segments:
			a, b = segments.popleft()

			for c, d, delta in mapping:
				partial_left  = c <= a < d
				partial_right = c < b <= d

				if partial_left and partial_right:
					processed.append((a + delta, b + delta))
					break

				if partial_left:
					processed.append((a + delta, d + delta))
					segments.append((d, b))
					break

				if partial_right:
					processed.append((c + delta, b + delta))
					segments.append((a, c))
					break

				if a < c and b > d:
					processed.append((c + delta, d + delta))
					segments.append((a, c))
					segments.append((d, b))
					break
			else:
				processed.append((a, b))

		segments = processed

	return min(map(itemgetter(0), segments))


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

seeds, mappings = parse_input(fin)

segments = deque((s, s + 1) for s in seeds)
ans = solve(segments, mappings)
print('Part 1:', ans)

segments = deque((a, a + b) for a, b in zip(seeds[::2], seeds[1::2]))
ans = solve(segments, mappings)
print('Part 2:', ans)
