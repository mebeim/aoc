#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 2)
fin = advent.get_input()

lines = read_lines(fin)

red = 12
green = 13
blue = 14
ans1 = ans2 = 0

for line in lines:
	minred = 0
	mingreen = 0
	minblue = 0

	gid, line = line.split(': ')
	gid = int(re.findall(r'\d+', gid)[0])
	bad = False

	for x in line.split('; '):
		nred = re.findall(r'(\d+) red', x)
		ngreen = re.findall(r'(\d+) green', x)
		nblue = re.findall(r'(\d+) blue', x)

		if nred: nred = int(nred[0])
		else: nred = 0

		if ngreen: ngreen = int(ngreen[0])
		else: ngreen = 0

		if nblue: nblue = int(nblue[0])
		else: nblue = 0

		if nred > red or nblue > blue or ngreen > green:
			bad = True

		minred = max(minred, nred)
		minblue = max(minblue, nblue)
		mingreen = max(mingreen, ngreen)

	ans2 += minred * mingreen * minblue

	if not bad:
		ans1 += gid


advent.print_answer(1, ans1)
advent.print_answer(2, ans2)
