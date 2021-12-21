#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 21)
DEBUG = 'debug' in map(str.lower, sys.argv)

if not DEBUG:
	fin = advent.get_input()
	p1start = int(re.findall('\d+', next(fin))[1])
	p2start = int(re.findall('\d+', next(fin))[1])
else:
	p1start = 4
	p2start = 8

timer_start()

p1 = p1start
p2 = p2start
p1score = 0
p2score = 0
die = 1
rolls = 0

while 1:
	p1 += die
	die += 1
	if die > 100: die = 1
	p1 += die
	die += 1
	if die > 100: die = 1
	p1 += die
	die += 1
	if die > 100: die = 1

	rolls += 3

	while p1 > 10:
		p1 -= 10
	p1score += p1
	# print('1:', die, ':', p1, ':', p1score)

	if p1score >= 1000:
		loser_score = p2score
		break

	p2 += die
	die += 1
	if die > 100: die = 1
	p2 += die
	die += 1
	if die > 100: die = 1
	p2 += die
	die += 1
	if die > 100: die = 1
	rolls += 3

	while p2 > 10:
		p2 -= 10
	p2score += p2
	# print('2:', die, ':', p2, ':', p2score)

	if p2score >= 1000:
		loser_score = p1score
		break

# print(rolls)
# print(loser_score)
ans = rolls * loser_score

advent.print_answer(1, ans)
# wait('Submit? ')
# advent.submit_answer(1, ans)

dicerolls = tuple(map(sum, product(range(1, 4), range(1, 4), range(1, 4))))

def doturn(game):
	p1wins = 0
	p2wins = 0
	newgame = defaultdict(int)

	# advance all universes
	for key, n in game.items():
		# eprint(key, n)

		p1pos, p2pos, p1score, p2score, who = key

		if who == 1:
			# p1 plays
			for roll in dicerolls:
				p1newpos = p1pos + roll
				while p1newpos > 10:
					p1newpos -= 10

				p1newscore = p1score + p1newpos

				if p1newscore >= 21:
					p1wins += n
				else:
					newgame[p1newpos, p2pos, p1newscore, p2score, 2] += n
		else:
			# p2 plays
			for roll in dicerolls:
				p2newpos = p2pos + roll
				while p2newpos > 10:
					p2newpos -= 10

				p2newscore = p2score + p2newpos

				if p2newscore >= 21:
					p2wins += n
				else:
					newgame[p1pos, p2newpos, p1score, p2newscore, 1] += n

	return newgame, p1wins, p2wins


ans = 0
# NOPE can't work
# p1 = defaultdict(int, {(6, 0): 1}) # (pos, score) -> n of universes
# p2 = defaultdict(int, {(4, 0): 1}) # (pos, score) -> n of universes

# (p1pos, p2pos, p1score, p2score, turn_of_who) -> n of universes
# game = defaultdict(int, {(4, 8, 0, 0, 1): 1}) # example
game = defaultdict(int, {(p1start, p2start, 0, 0, 1): 1})

p1tot = p2tot = 0

while game:
	game, a, b = doturn(game)
	p1tot += a
	p2tot += b

ans = max(p1tot, p2tot)

# if DEBUG:
# 	eprint('got     :', ans)
# 	eprint('expected:', 444356092776315)
# 	if ans != 444356092776315:
# 		sys.exit(0)

advent.print_answer(2, ans)
# wait('Submit? ')
# advent.submit_answer(2, ans)
