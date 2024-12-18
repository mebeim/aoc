#!/usr/bin/env python3

import sys


def safe(ints, allow_removal=False):
	for i in range(len(ints) - 1):
		if not 1 <= ints[i + 1] - ints[i] <= 3:
			break
	else:
		return True

	if not allow_removal:
		return False

	# Try removing ints[i]
	rest = ints[i - 1:i] + ints[i + 1:]

	for j in range(len(rest) - 1):
		if not 1 <= rest[j + 1] - rest[j] <= 3:
			if j > 0:
				return False
			break
	else:
		return True

	# Try removing ints[i + 1]
	rest = ints[i:i + 1] + ints[i + 2:]

	for j in range(len(rest) - 1):
		if not 1 <= rest[j + 1] - rest[j] <= 3:
			return False

	return True


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

n_safe = n_safe_with_removal = 0

for line in fin:
	ints = list(map(int, line.split()))

	if safe(ints) or safe(ints[::-1]):
		n_safe += 1
		continue

	if safe(ints, True) or safe(ints[::-1], True):
		n_safe_with_removal += 1

n_safe_with_removal += n_safe

print('Part 1:', n_safe)
print('Part 2:', n_safe_with_removal)
