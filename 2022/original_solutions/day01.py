#!/usr/bin/env python3

from utils.all import *

advent.setup(2022, 1)
fin = advent.get_input()

chunks = [[]]

for line in fin:
	if not line.strip():
		chunks.append([])
	else:
		chunks[-1].append(int(line))

ans = max(map(sum, chunks))
advent.print_answer(1, ans)

chunks = sorted(chunks, key=lambda x:sum(x), reverse=1)
ans = sum(map(sum, chunks[:3]))
advent.print_answer(2, ans)
