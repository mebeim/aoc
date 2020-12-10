#!/usr/bin/env python3

from utils import advent
import re
from collections import defaultdict
from functools import lru_cache

def count_can_contain(G, src, visited=set()):
	for color in G[src]:
		if color not in visited:
			visited.add(color)
			count_can_contain(G, color, visited)

	return len(visited)

@lru_cache()
def count_contained(src):
	tot = 0
	for qty, color in contains[src]:
		tot += qty * (1 + count_contained(color))

	return tot


advent.setup(2020, 7)
fin = advent.get_input()

contained_by = defaultdict(list)
contains     = defaultdict(list)
inner_exp    = re.compile(r'(\d+) ([\w ]+) bags?[.,]')

for line in fin:
	outer, inners = line.split(' bags contain ')
	inners = inner_exp.findall(inners)

	for qty, inner in inners:
		contained_by[inner].append(outer)
		contains[outer].append((int(qty), inner))

can_contain_gold = count_can_contain(contained_by, 'shiny gold')
advent.print_answer(1, can_contain_gold)

total_bags = count_contained('shiny gold')
advent.print_answer(2, total_bags)
