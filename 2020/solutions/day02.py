#!/usr/bin/env python3

from utils import advent
import re

advent.setup(2020, 2)
fin = advent.get_input()

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

advent.print_answer(1, valid1)
advent.print_answer(2, valid2)
