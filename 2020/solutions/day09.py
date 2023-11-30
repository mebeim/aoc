#!/usr/bin/env python3

import sys

def two_sum(nums, target):
	compls = set()

	for x in nums:
		if x in compls:
			return True

		compls.add(target - x)

	return False


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

nums = tuple(map(int, fin.readlines()))

for i, target in enumerate(nums[25:]):
	if not two_sum(nums[i:i + 25], target):
		break

print('Part 1:', target)


cusums = [0]
a, b = 0, 0

while 1:
	partsum = cusums[b] - cusums[a]

	if partsum < target:
		cusums.append(cusums[-1] + nums[b])
		b += 1
	elif partsum > target:
		a += 1
	else:
		break

subseq = nums[a:b + 1]
ans = min(subseq) + max(subseq)

print('Part 2:', ans)
