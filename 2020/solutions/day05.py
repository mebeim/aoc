#!/usr/bin/env python3

from utils import advent
from itertools import product

advent.setup(2020, 5)
fin = advent.get_input()

table  = str.maketrans('BFRL', '1010')
seats  = fin.read().translate(table).splitlines()
ids    = tuple(map(lambda s: int(s, 2), seats))
max_id = max(ids)

advent.print_answer(1, max_id)

min_id   = min(ids)
expected = max_id * (max_id + 1) // 2 - min_id * (min_id - 1) // 2
my_id    = expected - sum(ids)

advent.print_answer(2, my_id)
