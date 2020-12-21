#!/usr/bin/env python3

from utils import advent
from collections import defaultdict

def parse_input(fin):
	recipes = []
	possible_allers = defaultdict(set)
	recipes_with    = defaultdict(list)

	for i, line in enumerate(fin):
		ingredients, allergens = line.rstrip(')\n').split(' (contains ')

		ingredients = set(ingredients.split())
		allergens   = set(allergens.split(', '))
		recipes.append(ingredients)

		for aller in allergens:
			recipes_with[aller].append(i)

		for ingr in ingredients:
			possible_allers[ingr] |= allergens

	return recipes, possible_allers, recipes_with

def safe_ingredients(recipes, possible_allers, recipes_with):
	safe = []

	for ingr, possible in possible_allers.items():
		impossible = set()

		for aller in possible:
			if any(ingr not in recipes[i] for i in recipes_with[aller]):
				impossible.add(aller)

		possible -= impossible
		if not possible:
			safe.append(ingr)

	return safe

def simplify(possible_allers):
	assigned = {}

	while possible_allers:
		for ingr, possible in possible_allers.items():
			if len(possible) == 1:
				break

		aller = possible.pop()
		assigned[aller] = ingr
		del possible_allers[ingr]

		for ingr, possible in possible_allers.items():
			if aller in possible:
				possible.remove(aller)

	return assigned


advent.setup(2020, 21)
fin = advent.get_input()

recipes, possible_allers, recipes_with = parse_input(fin)

safe = safe_ingredients(recipes, possible_allers, recipes_with)
tot  = sum(ingr in r for r in recipes for ingr in safe)

advent.print_answer(1, tot)


for ingr in safe:
	del possible_allers[ingr]

assigned = simplify(possible_allers)
lst = ','.join(map(assigned.get, sorted(assigned)))

advent.print_answer(2, lst)
