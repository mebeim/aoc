#!/usr/bin/env python3

import sys
from functools import cache

@cache
def solve(record, groups, curlen=0):
	if not record:
		return not groups and curlen == 0 or len(groups) == 1 and groups[0] == curlen

	if groups and curlen > groups[0] or not groups and curlen:
		return False

	char, record = record[0], record[1:]
	total = 0

	if char in '#?':
		total += solve(record, groups, curlen + 1)

	if char in '.?':
		if not curlen:
			total += solve(record, groups, 0)
		elif curlen == groups[0]:
			total += solve(record, groups[1:], 0)

	return total


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

total1 = total2 = 0

for line in fin:
	records, groups = line.split()
	groups = tuple(map(int, groups.split(',')))

	total1 += solve(records, groups)
	solve.cache_clear()

	total2 += solve('?'.join([records] * 5), groups * 5)
	solve.cache_clear()

print('Part 1:', total1)
print('Part 2:', total2)
