#!/usr/bin/env python3

import sys
from itertools import product

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

table  = str.maketrans('BFRL', '1010')
seats  = fin.read().translate(table).splitlines()
ids    = tuple(map(lambda s: int(s, 2), seats))
max_id = max(ids)

print('Part 1:', max_id)

min_id   = min(ids)
expected = max_id * (max_id + 1) // 2 - min_id * (min_id - 1) // 2
my_id    = expected - sum(ids)

print('Part 2:', my_id)
