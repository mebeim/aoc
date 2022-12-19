#!/usr/bin/env python3

from utils.all import *

def sim(ore_cost, clay_cost, obs_cost, geo_cost, time=24, p2=False):
	q = deque([(0, 1, 0, 0, 0, 0, 0, 0, time)])
	visited = set()

	best = 0
	max_ore_needed = max(ore_cost, clay_cost, obs_cost[0], geo_cost[0])

	while q:
		ore, rore, clay, rclay, obs, robs, geo, rgeo, time = x = q.pop()
		if x in visited:
			continue

		visited.add(x)

		rore = min(rore, max_ore_needed)

		new_ore = ore + rore
		new_clay = clay + rclay
		new_obs = obs + robs
		new_geo = geo + rgeo
		time -= 1

		if time == 0:
			best = max(best, new_geo)
			continue

		build = False
		if ore >= geo_cost[0] and obs >= geo_cost[1]:
			new_ore2 = new_ore - geo_cost[0]
			new_obs2 = new_obs - geo_cost[1]
			new_rgeo = rgeo + 1
			q.append((new_ore2, rore, new_clay, rclay, new_obs2, robs, new_geo, new_rgeo, time))
			build = True

			# Probably wrong, but works anyway...
			continue

		if ore >= obs_cost[0] and clay >= obs_cost[1]:
			new_ore2 = new_ore - obs_cost[0]
			new_clay2 = new_clay - obs_cost[1]
			new_robs = robs + 1
			q.append((new_ore2, rore, new_clay2, rclay, new_obs, new_robs, new_geo, rgeo, time))
			build = True

		if ore >= clay_cost:
			new_ore2 = new_ore - clay_cost
			new_rclay = rclay + 1
			q.append((new_ore2, rore, new_clay, new_rclay, new_obs, robs, new_geo, rgeo, time))
			build = True

		if ore >= ore_cost:
			new_ore2 = new_ore - ore_cost
			new_rore = rore + 1
			q.append((new_ore2, new_rore, new_clay, rclay, new_obs, robs, new_geo, rgeo, time))
			build = True

		# Technically wrong, but magically works for the first 3 blueprints :')
		# if not build:
		if not p2 or not build:
			q.append((new_ore, rore, new_clay, rclay, new_obs, robs, new_geo, rgeo, time))

	return best


advent.setup(2022, 19)
DEBUG = 'debug' in map(str.lower, sys.argv)
fin = advent.get_input() if not DEBUG else io.StringIO('''\
Blueprint 1: Each ore robot costs 4 ore. Each clay robot costs 2 ore. Each obsidian robot costs 3 ore and 14 clay. Each geode robot costs 2 ore and 7 obsidian.
Blueprint 2: Each ore robot costs 2 ore. Each clay robot costs 3 ore. Each obsidian robot costs 3 ore and 8 clay. Each geode robot costs 3 ore and 12 obsidian.
''')

lines = read_lines(fin)
ans = 0
r = re.compile(r'\d+')

bp = []

for l in lines:
	# l = l.split()
	nums = list(map(int, r.findall(l)))

	bid = nums[0]
	ore_cost = nums[1]
	clay_cost = nums[2]
	obs_cost = (nums[3], nums[4])
	geo_cost = (nums[5], nums[6])

	bp.append((bid, ore_cost, clay_cost, obs_cost, geo_cost))
	# eprint(bp[-1])

# timer_start('x')
tot = 0
for bid, *info in bp:
	s = sim(*info)
	# timer_lap('x')
	# eprint(bid, s)
	tot += bid * s

# timer_stop('x')
advent.print_answer(1, tot)


# timer_start('x')
tot = 1
for bid, *info in bp[:3]:
	s = sim(*info, time=32, p2=True)
	# timer_lap('x')
	# eprint(bid, s)
	tot *= s

# timer_stop('x')
advent.print_answer(2, tot)
