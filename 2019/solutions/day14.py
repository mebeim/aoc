#!/usr/bin/env python3

from utils import advent
from math import ceil
from collections import deque, defaultdict

def needed_ore(recipes, fuel_qty):
	queue = deque([(fuel_qty, 'FUEL')])
	leftover = defaultdict(int)
	total_ore = 0

	while queue:
		needed_qty, chemical = queue.popleft()

		if chemical == 'ORE':
			total_ore += needed_qty
			continue

		if leftover[chemical] >= needed_qty:
			leftover[chemical] -= needed_qty
			continue

		needed_qty -= leftover[chemical]
		leftover[chemical] = 0

		recipe_qty, ingredients = recipes[chemical]
		multiplier = ceil(needed_qty / recipe_qty)

		for qty, el in ingredients:
			queue.append((qty * multiplier, el))

		leftover[chemical] += multiplier * recipe_qty - needed_qty

	return total_ore


advent.setup(2019, 14)
fin = advent.get_input()

recipes = {}

for line in map(str.rstrip, fin):
	left, right = line.split(' => ')
	product_qty, product_name = right.split()

	ingredients = []
	for el in left.split(', '):
		qty, name = el.split()
		ingredients.append((int(qty), name))

	recipes[product_name] = (int(product_qty), ingredients)

ore = needed_ore(recipes, 1)
advent.print_answer(1, ore)


AVAILABLE_ORE = 10**12

hi = 2
while needed_ore(recipes, hi) < AVAILABLE_ORE:
	hi *= 2

lo = hi//2

while hi - lo > 1:
	x = (lo + hi) // 2
	ore = needed_ore(recipes, x)

	if ore > AVAILABLE_ORE:
		hi = x
	else:
		lo = x

advent.print_answer(2, lo)
