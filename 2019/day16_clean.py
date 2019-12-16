#!/usr/bin/env python3

import advent
advent.setup(2019, 16, dry_run=True)
fin = advent.get_input()

original = list(map(int, fin.read().strip()))
nums = original[:]
length = len(nums)

for _ in range(100):
	old = nums[:]

	for i in range(length//2 + 1):
		j = i
		m = i + 1
		cur = 0

		while j < length:
			cur += sum(old[j:j + m])
			j += 2 * m

			cur -= sum(old[j:j + m])
			j += 2 * m

		nums[i] = abs(cur) % 10

	for i in range(length - 2, length//2, -1):
		nums[i] += nums[i + 1]
		nums[i] %= 10

ans = ''.join(map(str, nums[:8]))

assert ans == '84487724'
advent.submit_answer(1, ans)


skip = int(''.join(map(str, original[:7])))
nums = (original * 10000)[skip:]
length = len(nums)

for step in range(100):
	for i in range(length - 2, -1, -1):
		nums[i] += nums[i + 1]
		nums[i] %= 10

ans2 = ''.join(map(str, nums[:8]))

assert ans2 == '84692524'
advent.submit_answer(2, ans2)
