#!/usr/bin/env python3

from utils.all import *

advent.setup(2022, 6)
fin = advent.get_input()

ans = 0
data = fin.read().strip()

for i in range(len(data)):
	if len(set(data[i:i + 4])) == 4:
		ans = i + 4
		break


advent.print_answer(1, ans)


ans = 0
for i in range(len(data)):
	if len(set(data[i:i + 14])) == 14:
		ans = i + 14
		break

advent.print_answer(2, ans)
