#!/usr/bin/env python3

import re
from math import prod
from collections import deque

import sys

def best_case_scenario(initial_amount, robots, t):
	return initial_amount + robots * (t + 1) + t * (t + 1) // 2

ORE, CLAY, OBS, GEO = (1 << i for i in range(4))

def search(blueprint, time=24):
	rore_cost, rclay_cost, robs_cost_ore, robs_cost_clay, rgeo_cost_ore, rgeo_cost_obs = blueprint
	max_ore_needed  = max(rore_cost, rclay_cost, robs_cost_ore, rgeo_cost_ore)
	max_clay_needed = robs_cost_clay
	max_obs_needed  = rgeo_cost_obs

	best = 0
	visited = set()
	q = deque([(time, 0, 0, 0, 0, 1, 0, 0, 0, 0)])

	while q:
		tmp = q.pop()

		state = tmp[:-1]
		if state in visited:
			continue

		visited.add(state)

		time, ore, clay, obs, geo, rore, rclay, robs, rgeo, did_not_build = tmp
		newore  = ore  + rore
		newclay = clay + rclay
		newobs  = obs  + robs
		newgeo  = geo  + rgeo
		time -= 1

		if time == 0:
			best = max(best, newgeo)
			continue

		if best_case_scenario(newgeo, rgeo, time) < best:
			continue

		if best_case_scenario(newobs, robs, time) < rgeo_cost_obs \
			or best_case_scenario(newore, rore, time) < rgeo_cost_ore:
			best = max(best, newgeo + rgeo * time)
			continue

		can_build = 0

		if obs >= rgeo_cost_obs and ore >= rgeo_cost_ore and not (did_not_build & GEO):
			can_build |= GEO
			q.append((time, newore - rgeo_cost_ore, newclay, newobs - rgeo_cost_obs, newgeo, rore, rclay, robs, rgeo + 1, 0))

		if robs < max_obs_needed and clay >= robs_cost_clay and ore >= robs_cost_ore and not (did_not_build & OBS):
			can_build |= OBS
			q.append((time, newore - robs_cost_ore, newclay - robs_cost_clay, newobs, newgeo, rore, rclay, robs + 1, rgeo, 0))

		if rclay < max_clay_needed and ore >= rclay_cost and not (did_not_build & CLAY):
			can_build |= CLAY
			q.append((time, newore - rclay_cost, newclay, newobs, newgeo, rore, rclay + 1, robs, rgeo, 0))

		if rore < max_ore_needed and ore >= rore_cost and not (did_not_build & ORE):
			can_build |= ORE
			q.append((time, newore - rore_cost, newclay, newobs, newgeo, rore + 1, rclay, robs, rgeo, 0))

		if (robs and obs < max_obs_needed) or (rclay and clay < max_clay_needed) or ore < max_ore_needed:
			q.append((time, newore, newclay, newobs, newgeo, rore, rclay, robs, rgeo, can_build))

	return best


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

exp = re.compile(r'\d+')
blueprints = []

for line in fin:
	blueprints.append(tuple(map(int, exp.findall(line))))

total = sum(bid * search(b) for bid, *b in blueprints)
print('Part 1:', total)


total = prod(search(b, 32) for _, *b in blueprints[:3])
print('Part 2:', total)
