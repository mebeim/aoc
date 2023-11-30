#!/usr/bin/env python3

import sys
import re

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

data     = fin.read()
rexp     = re.compile(r'(\d+)-(\d+) (\w): (\w+)')
policies = rexp.findall(data)

valid1, valid2 = 0, 0

for mmin, mmax, letter, password in policies:
	mmin, mmax = int(mmin), int(mmax)

	if mmin <= password.count(letter) <= mmax:
		valid1 += 1

	if (password[mmin - 1] == letter) ^ (password[mmax - 1] == letter):
		valid2 += 1

print('Part 1:', valid1)
print('Part 2:', valid2)
