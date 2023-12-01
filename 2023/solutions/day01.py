#!/usr/bin/env python3

import sys

def check_digit(string):
	if string[0].isdigit():
		return int(string[0])

	d = next(filter(string.startswith, DIGITS), None)
	return DIGITS.get(d, 0)

DIGITS = {
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

total1 = total2 = 0

for line in fin:
	total1 += 10 * int(next(filter(str.isdigit, line)))
	total1 += int(next(filter(str.isdigit, line[::-1])))

	for i in range(len(line)):
		a = check_digit(line[i:])
		if a:
			break

	for i in range(len(line) - 1, -1, -1):
		b = check_digit(line[i:])
		if b:
			break

	total2 += 10 * a + b

	# Cursed alternative one-liner for part 2:
	# total2 += 10 * next(filter(None, map(check_digit, (line[i:] for i in range(len(line))))))
	# total2 += next(filter(None, map(check_digit, (line[i:] for i in range(len(line) -1, -1, -1)))))

print('Part 1:', total1)
print('Part 2:', total2)
