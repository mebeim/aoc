#!/usr/bin/env python3

from utils.all import *

advent.setup(2018, 24)
# fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

class Group:
	def __init__(self, units, hp, weak, immune, atk, atk_type, initiative, identifier):
		self.units      = units
		self.hp         = hp
		self.weak       = set(weak)
		self.immune     = set(immune)
		self.atk        = atk
		self.atk_type   = atk_type
		self.initiative = initiative
		self.id         = identifier
		self.army       = None
		self.target     = None
		self.lost_units = False

	def __repr__(self):
		gid = 'I' if self.army.name == 'Immune System' else 'X' if self.army.name == 'Infection' else 'G'

		return '{}{:d}({}u {}hp {}ep {}{} {}i {}/{})'.format(
			gid,
			self.id,
			self.units,
			self.hp,
			self.effective_power(),
			self.atk,
			self.atk_type,
			self.initiative,
			'-' if not self.immune else ''.join(self.immune),
			'-' if not self.weak else ''.join(self.weak)
		)

	def effective_power(self):
		return self.atk * self.units

	def calculate_damage(self, attacker):
		if attacker.atk_type in self.immune:
			return 0

		dmg = attacker.effective_power()

		if attacker.atk_type in self.weak:
			dmg *= 2

		return dmg

	# @log_calls(log_return=False)
	def choose_target(self, enemy_groups):
		self.target = None

		if not enemy_groups:
			return

		chosen = max(enemy_groups, key=lambda g: (
				g.calculate_damage(self),
				g.effective_power(),
				g.initiative
			)
		)

		if chosen.calculate_damage(self) == 0:
			self.target = None
		else:
			self.target = chosen
			enemy_groups.remove(self.target)

		# eprint('->', self.target)

	# @log_calls(log_return=False)
	def receive_attack(self, enemy):
		dmg             = self.calculate_damage(enemy)
		dead_units      = dmg // self.hp
		self.units      = max(self.units - dead_units, 0)
		self.lost_units = dead_units > 0

		if self.units == 0:
			self.army.groups.remove(self)

	def alive(self):
		return self.units > 0

class Army:
	def __init__(self, name, groups):
		self.name             = name
		self.groups           = groups

		for g in self.groups:
			g.army = self

	def __getitem__(self, k):
		return self.groups[k]

	def __repr__(self):
		s = '{}:'.format(self.name)

		if not self.groups:
			return s + ' DEAD.'

		for i, g in enumerate(self.groups):
			s += '\n {:2d}: {}'.format(i, repr(g))

		return s

	def prepare_for_fight(self):
		for group in self.groups:
			group.lost_units = False

	def choose_targets(self, enemy):
		enemy_groups = enemy.groups[:]

		for group in sorted(
				self.groups,
				key=lambda g: (g.effective_power(), g.initiative),
				reverse=True
			):
			group.choose_target(enemy_groups)

	def alive(self):
		return len(self.groups) > 0

def get_armies(atk_boost):
	a = Army('Immune System', [
		Group(8808, 5616 , (RADIATION)             , (COLD)                     , 5    + atk_boost, BLUDGEONING, 10, 1 ),
		Group(900 , 13511, (RADIATION)             , ()                         , 107  + atk_boost, RADIATION  , 20, 2 ),
		Group(581 , 10346, (RADIATION)             , (SLASHING)                 , 140  + atk_boost, FIRE       , 14, 3 ),
		Group(57  , 9991 , (BLUDGEONING)           , (SLASHING, RADIATION, FIRE), 1690 + atk_boost, FIRE       , 4 , 4 ),
		Group(4074, 6549 , (FIRE)                  , ()                         , 15   + atk_boost, RADIATION  , 2 , 5 ),
		Group(929 , 5404 , ()                      , (BLUDGEONING, RADIATION)   , 45   + atk_boost, FIRE       , 16, 6 ),
		Group(2196, 3186 , (FIRE)                  , (RADIATION)                , 10   + atk_boost, FIRE       , 11, 7 ),
		Group(4420, 9691 , (RADIATION)             , (FIRE)                     , 21   + atk_boost, FIRE       , 7 , 8 ),
		Group(3978, 2306 , (COLD, RADIATION)       , ()                         , 4    + atk_boost, FIRE       , 12, 9 ),
		Group(1284, 4487 , (RADIATION, BLUDGEONING), ()                         , 32   + atk_boost, SLASHING   , 19, 10)
	])

	b = Army('Infection', [
		Group(4262, 23427, (SLASHING)         , (FIRE)     , 9  , SLASHING   , 8 , 1 ),
		Group(217 , 9837 , (BLUDGEONING)      , ()         , 73 , BLUDGEONING, 1 , 2 ),
		Group(5497, 33578, (RADIATION, COLD)  , ()         , 11 , SLASHING   , 17, 3 ),
		Group(866 , 41604, (COLD)             , ()         , 76 , RADIATION  , 15, 4 ),
		Group(1823, 19652, (FIRE, COLD)       , ()         , 20 , SLASHING   , 13, 5 ),
		Group(2044, 23512, (COLD)             , ()         , 22 , SLASHING   , 9 , 6 ),
		Group(373 , 40861, ()                 , (COLD)     , 215, SLASHING   , 18, 7 ),
		Group(5427, 43538, (BLUDGEONING)      , (RADIATION), 15 , SLASHING   , 5 , 8 ),
		Group(3098, 19840, (BLUDGEONING, COLD), ()         , 12 , RADIATION  , 3 , 9 ),
		Group(785 , 14669, ()                 , ()         , 30 , FIRE       , 6 , 10)
	])

	# a = Army('Immune System', [
	# 	Group(17, 5390, (RADIATION, BLUDGEONING), (), 4507 + atk_boost, FIRE, 2, 1),
	# 	Group(989, 1274, (SLASHING, BLUDGEONING), (FIRE), 25 + atk_boost, SLASHING, 3, 2),
	# ])

	# b = Army('Infection', [
	# 	Group(801, 4706, (RADIATION), (), 116, BLUDGEONING, 1, 1),
	# 	Group(4485, 2961, (FIRE, COLD), (RADIATION), 12, SLASHING, 4, 2),
	# ])

	return a, b

def battle(atk_boost=0):
	immune_system, infection = armies = get_armies(atk_boost)
	groups_by_initiative = sorted(immune_system.groups + infection.groups, key=lambda g: g.initiative, reverse=True)

	# eprint(immune_system)
	# eprint(infection)

	while immune_system.alive() and infection.alive():
		# eprint('-'*30)

		infection.choose_targets(immune_system)
		immune_system.choose_targets(infection)

		for a in armies:
			a.prepare_for_fight()

		dead_groups = set()

		for g in groups_by_initiative:
			if g.alive() and g.target is not None and g.target.alive():
				dead = g.target.receive_attack(g)

				if dead:
					dead_groups.add(g.target)

		if not any(g.lost_units for g in groups_by_initiative):
			break

		groups_by_initiative = list(filter(Group.alive, groups_by_initiative))

		# eprint(immune_system)
		# eprint(infection)

	if sum(a.alive() for a in armies) == 1:
		winner      = next(filter(Army.alive, armies))
		winner_name = winner.name
		alive_units = sum(g.units for g in winner.groups)
	else:
		winner_name = 'None'
		alive_units = -1

	return winner_name, alive_units


FIRE, COLD, RADIATION, SLASHING, BLUDGEONING = 'FCRSB' #= range(5)

_, alive_units = battle()

advent.submit_answer(1, alive_units)

# for test in range(100):
# 	print(test, '->', battle(test))
# sys.exit(0)

l, r = 0, 10000

while l != r:
	atk_boost = (l + r) // 2
	# eprint(l, r, atk_boost)

	winner, _ = battle(atk_boost)

	# eprint(winner)

	if winner != 'Immune System':
		l = atk_boost + 1
	else:
		r = atk_boost

_, alive_units = battle(l)

# 20816 too high
# 2193 not right
advent.submit_answer(2, alive_units)
