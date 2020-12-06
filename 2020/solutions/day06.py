#!/usr/bin/env python3

from utils import advent
from functools import reduce, partial

advent.setup(2020, 6)
fin = advent.get_input()

into_sets = partial(map, set)
unionize  = partial(reduce, set.union)
intersect = partial(reduce, set.intersection)

raw_groups = fin.read().split('\n\n')
groups     = tuple(map(tuple, map(into_sets, map(str.splitlines, raw_groups))))

n_any_yes = sum(map(len, map(unionize, groups)))
n_all_yes = sum(map(len, map(intersect, groups)))

advent.print_answer(1, n_any_yes)
advent.print_answer(2, n_all_yes)
