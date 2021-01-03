#!/usr/bin/env python3

from utils import advent

advent.setup(2020, 6)
fin = advent.get_input()

groups = fin.read().split('\n\n')
groups = tuple(map(lambda g: tuple(map(set, g.splitlines())), groups))

n_any_yes = sum(len(set.union(*g)) for g in groups)
n_all_yes = sum(len(set.intersection(*g)) for g in groups)

advent.print_answer(1, n_any_yes)
advent.print_answer(2, n_all_yes)
