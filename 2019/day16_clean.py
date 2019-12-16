#!/usr/bin/env python3

import advent

advent.setup(2019, 16, dry_run=True)
fin = advent.get_input()

original = list(map(int, fin.read().strip()))
digits = original[:]
length = len(digits)

for _ in range(100):
	old = digits[:]

	for i in range(length//2 + 1):
		j = i
		step = i + 1
		cur = 0

		while j < length:
			cur += sum(old[j:j + step])
			j += 2 * step

			cur -= sum(old[j:j + step])
			j += 2 * step

		digits[i] = abs(cur) % 10

	cusum = 0
	for i in range(length - 1, length//2, -1):
		cusum += digits[i]
		digits[i] = cusum % 10

answer = ''.join(map(str, digits[:8]))

assert answer == '84487724'
advent.submit_answer(1, answer)


skip = int(''.join(map(str, original[:7])))
assert skip >= len(original)/2

digits = (original * 10000)[skip:]
length = len(digits)

for _ in range(100):
	cusum = 0
	for i in range(length - 1, -1, -1):
		cusum += digits[i]
		digits[i] = cusum % 10

answer = ''.join(map(str, digits[:8]))

assert answer == '84692524'
advent.submit_answer(2, answer)
