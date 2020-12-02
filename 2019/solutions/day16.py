#!/usr/bin/env python3

from utils import advent

advent.setup(2019, 16)
fin = advent.get_input()

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
advent.print_answer(1, answer)


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
advent.print_answer(2, answer)
