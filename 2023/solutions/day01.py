#!/usr/bin/env python3

import sys

def check_number(char, line):
	if char.isdigit():
		return int(char)
	else:
		for num in NUMBERS:
			if line.startswith(num):
				return NUMBERS[num]

	return 0


NUMBERS = {
	'zero' : 0,
	'one'  : 1,
	'two'  : 2,
	'three': 3,
	'four' : 4,
	'five' : 5,
	'six'  : 6,
	'seven': 7,
	'eight': 8,
	'nine' : 9,
}

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

lines = fin.readlines()
total = 0

for line in lines:
	total += 10 * int(next(filter(str.isdigit, line)))
	total += int(next(filter(str.isdigit, line[::-1])))

print('Part 1:', total)


total = 0

for line in lines:
	for i, char in enumerate(line):
		n = check_number(char, line[i:])
		if n:
			total += 10 * n
			break

	for i in range(len(line) - 1, -1, -1):
		n = check_number(line[i], line[i:])
		if n:
			total += n
			break

print('Part 2:', total)
