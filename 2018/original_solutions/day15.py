#!/usr/bin/env python3

from utils import advent

import sys
import copy
import networkx as nx
from sortedcontainers import SortedKeyList

advent.setup(2018, 15, True)
fin = advent.get_input()
# print(*fin)

##################################################

class Ripperoni(Exception):
	pass

def log(s, *a):
	if LOG:
		sys.stderr.write(s.format(*a))
		sys.stderr.flush()

def dump():
	log('   ' + ' '*10 + '1'*10 + '2'*10 + '3'*10 + '\n')
	log('   ' + '0123456789'*4 + '\n')

	for i, row in enumerate(cavern):
		log('{:>2d} ', i)
		for j, cell in enumerate(row):
			if (i, j) in elves:
				log(ELF)
			elif (i, j) in goblins:
				log(GOBLIN)
			elif cell != WALL:
				log(FREE)
			else:
				log(WALL)
		log('\n')

def adjacent(i, j):
	yield i-1, j
	yield i  , j-1
	yield i  , j+1
	yield i+1, j

def connect(i, j):
	G.add_node((i, j))

	for ni, nj in adjacent(i, j):
		if (ni, nj) in G:
			G.add_edge((i, j), (ni, nj))

def disconnect(i, j):
	G.remove_node((i, j))

def iter_enemies(me):
	for e in filter(lambda u: u[4] != me[4], units):
		yield e

def enemies_of(me):
	if me[4] == ELF:
		return goblins
	return elves

def are_enemies_alive(me):
	return len(enemies_of(me)) > 0

def is_near_enemies(me):
	adj = adjacent(*me[:2])
	ene = enemies_of(me)

	return any(a in ene for a in adj)

def iter_near_enemies(me):
	ene = enemies_of(me)

	for a in adjacent(*me[:2]):
		if a in ene:
			yield ene[a]

def nearest_reachable_enemy(me):
	i, j, _, _, _ = me
	enemies = {}

	log('    Finding closest enemy to {},{}:\n', i, j)
	connect(i, j)

	for ei, ej in enemies_of(me):
		log('      {}, {}', ei, ej)
		connect(ei, ej)

		try:
			enemies[ei, ej] = nx.shortest_path_length(G, (i, j), (ei, ej))
			log(' -> {}\n', enemies[ei, ej])
		except nx.NetworkXNoPath:
			log(' -> no path.\n')
			pass

		disconnect(ei, ej)

	nearest, next_move = None, None

	if enemies:
		nearest = min(enemies, key=lambda e: (enemies[e], *e))

		connect(*nearest)
		next_move = min(map(lambda p: p[1], nx.all_shortest_paths(G, (i, j), nearest)))
		disconnect(*nearest)

	disconnect(i, j)

	log('    nearest: {}, next_move: {}\n', nearest, next_move)

	return nearest, next_move

def track(me):
	if me[4] == ELF:
		elves[me[0], me[1]] = me
	else:
		goblins[me[0], me[1]] = me

def untrack(me):
	if me[4] == ELF:
		elves.pop((me[0], me[1]))
	else:
		goblins.pop((me[0], me[1]))

def can_move(me): # assumes only FREE cells are in the graph
	return any(node in G for node in adjacent(me[0], me[1]))

def move(me, where):
	untrack(me)
	connect(*me[:2])
	disconnect(*where)
	me[:2] = where
	track(me)

	me[3] = is_near_enemies(me)

	for enemy in iter_near_enemies(me):
		enemy[3] = True

def die(me):
	if part2 and me[4] == ELF:
		raise Ripperoni()

	killer_allies = list(iter_near_enemies(me))

	connect(*me[:2])
	untrack(me)
	units.discard(me)

	for killer_ally in killer_allies:
		killer_ally[3] = is_near_enemies(killer_ally)

def hit(me):
	if me[4] == GOBLIN:
		me[2] -= elves_atk
	else:
		me[2] -= 3

	if me[2] <= 0:
		die(me)

def fight(me):
	near_enemies = list(iter_near_enemies(me))

	if near_enemies:
		best_enemy = min(near_enemies, key=lambda e: (e[2], e[0], e[1]))
		hit(best_enemy)

def take_turn(me):
	log('Turn of {}:\n', me)

	if not are_enemies_alive(me):
		return False

	if me[3]:
		log('  in combat\n')
		fight(me)
		return True

	elif can_move(me):
		log('  not in combat\n')
		enemy, next_cell = nearest_reachable_enemy(me)

		if enemy is not None and next_cell is not None:
			units.discard(me)

			move(me, next_cell)

			if me[3]:
				log('  went in combat\n')
				fight(me)

			units.add(me)

	return True

def do_round():
	cur_units = list(units)
	done = True

	for u in cur_units:
		if u[2] > 0:
			if take_turn(u[:]):
				done = False

	log('{}\n', elves.values())
	log('{}\n', goblins.values())
	# input('.'*50)

	return done

def setup(cavern, is_part2=False, elves_power=3):
	global units
	global elves
	global goblins
	global elves_atk
	global part2
	global G

	units     = SortedKeyList(key=lambda u: u[:2])
	elves     = {}
	goblins   = {}
	elves_atk = elves_power
	part2     = is_part2
	G         = nx.Graph()

	for i, row in enumerate(cavern):
		for j, cell in enumerate(row):
			if cell == FREE:
				G.add_node((i, j))
			elif cell != WALL:
				u = [i, j, 200, False, cell]
				units.add(u)

				if cell == ELF:
					elves[i, j] = u
				elif cell == GOBLIN:
					goblins[i, j] = u

	for u in units:
		u[3] = is_near_enemies(u)

	for i, j in G.nodes:
		for ni, nj in adjacent(i, j):
			if (ni, nj) in G: # assumes borders are all walls
				G.add_edge((i, j), (ni, nj))

# unit
# [0] i
# [1] j
# [2] hp
# [3] in_combat
# [4] identifier

LOG = False

WALL   = '#'
GOBLIN = 'G'
ELF    = 'E'
FREE   = '.'

cavern = list(map(lambda l: list(l.strip()), fin))

setup(cavern)

played_rounds = 0
dump()
while not do_round():
	dump()
	played_rounds += 1

winners = elves if elves else goblins
total_hp = sum(map(lambda w: w[2], winners.values()))

ans = (played_rounds-1)*total_hp
advent.submit_answer(1, ans)


min_atk = 4
max_atk = 50

while min_atk != max_atk:
	cur_atk = (min_atk + max_atk) // 2

	LOG = True
	log('[{}, {}] -> {}\n', min_atk, max_atk, cur_atk)
	log('Simulating...')
	LOG = False

	setup(cavern, True, cur_atk)

	try:
		played_rounds = 0
		dump()
		while not do_round():
			dump()
			played_rounds += 1

		LOG = True
		log(' all elves alive! {} atk is enough.\n', cur_atk)
		LOG = False

		max_atk = cur_atk

		total_hp = sum(map(lambda w: w[2], elves.values()))
		ans2 = (played_rounds-1)*total_hp

	except Ripperoni:
		LOG = True
		log(' some elves died, RIP. {} atk is not enough.\n', cur_atk)
		LOG = False

		min_atk = cur_atk + 1

# 54560 too low
# 58860 not correct
advent.submit_answer(2, ans2)
