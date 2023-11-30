#!/usr/bin/env python3

import sys

def find_start(data, header_len, start=0):
	for i in range(start, len(data) - header_len):
		if len(set(data[i:i + header_len])) == header_len:
			return i + header_len


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

data = fin.read()
sop = find_start(data, 4)
som = find_start(data, 14, sop)

print('Part 1:', sop)
print('Part 2:', som)
