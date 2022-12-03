#!/usr/bin/env python3

from utils.all import *

advent.setup(2022, 3)

fin = advent.get_input()
lines = get_lines(fin)
ans = 0

def prio(x):
	if 'a' <= x <= 'z':
		return ord(x) - ord('a') + 1
	return ord(x) - ord('A') + 27

for line in lines:
	l = line.strip()
	a, b = l[:len(l) // 2], l[len(l) // 2:]

	for c in a:
		if c in b:
			ans += prio(c)
			break


advent.print_answer(1, ans)


lst = []

for line in lines:
	l = line.strip()
	lst.append(l)

chunks = [lst[i:i+3] for i in range(0, len(lst), 3)]
# print(chunks)

ans2 = 0
for chunk in chunks:
	for elf in chunk:
		done = 0
		for c in elf:
			if all(c in e for e in chunk):
				ans2 += prio(c)
				done=1
				break
		if done: break

advent.print_answer(2, ans2)
