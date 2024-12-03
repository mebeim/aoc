#!/usr/bin/env python3

import sys
from re import findall

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

total1 = total2 = 0
enabled = True

for a, b, do, dont in findall(r"mul\((\d+),(\d+)\)|(do\(\))|(don't\(\))", fin.read()):
	if do or dont:
		enabled = bool(do)
	else:
		x = int(a) * int(b)
		total1 += x
		total2 += x * enabled

print('Part 1:', total1)
print('Part 2:', total2)
