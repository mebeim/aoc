#!/usr/bin/env python3

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

chunks = fin.read().split('\n\n')
chunks = [tuple(map(int, chunk.split())) for chunk in chunks]
chunks.sort(key=sum, reverse=True)

ans1 = sum(chunks[0])
ans2 = sum(map(sum, chunks[:3]))

print('Part 1:', ans1)
print('Part 2:', ans2)
