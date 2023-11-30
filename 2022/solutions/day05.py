#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

raw    = []
stacks = [None]
moves  = []

for line in fin:
	if line == '\n':
		break
	raw.append(line)

for i, column in enumerate(zip(*raw)):
	if i % 4 == 1:
		stacks.append(''.join(column[:-1]).lstrip())

for line in fin:
	line = line.split()
	moves.append((int(line[1]), int(line[3]), int(line[5])))

original = stacks[:]

for n, i, j in moves:
	chunk = stacks[i][:n][::-1]
	stacks[i] = stacks[i][n:]
	stacks[j] = chunk + stacks[j]

top = ''.join(s[0] for s in stacks[1:])
print('Part 1:', top)


stacks = original

for n, i, j in moves:
	chunk = stacks[i][:n]
	stacks[i] = stacks[i][n:]
	stacks[j] = chunk + stacks[j]

top = ''.join(s[0] for s in stacks[1:])
print('Part 2:', top)
