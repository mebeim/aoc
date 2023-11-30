#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

original_str = fin.read().strip()
original = list(map(int, original_str))
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
print('Part 1:', answer)


# Enclosing part 2 inside a function works faster since the LOAD_FAST opcode
# used for function local variables is way faster than the LOAD_GLOBAL opcode
# used ford global variables (and therefore in the main body of the script).

def part2(digits, skip):
	digits = (original*10000)[skip:]
	length = len(digits)

	assert skip > length//2

	for _ in range(100):
		cusum = 0
		for i in range(length - 1, -1, -1):
			cusum += digits[i]
			digits[i] = cusum % 10

	return ''.join(map(str, digits[:8]))

skip = int(''.join(original_str[:7]))
answer = part2(original, skip)
print('Part 2:', answer)
