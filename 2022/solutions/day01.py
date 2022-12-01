#!/usr/bin/env python3

from utils.all import *

advent.setup(2022, 1)
fin = advent.get_input()

chunks = fin.read().split('\n\n')
chunks = [tuple(map(int, chunk.split())) for chunk in chunks]
chunks.sort(key=sum, reverse=True)

ans1 = sum(chunks[0])
ans2 = sum(map(sum, chunks[:3]))

advent.print_answer(1, ans1)
advent.print_answer(2, ans2)
