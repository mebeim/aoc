#!/usr/bin/env python3

from utils.all import *

advent.setup(2023, 7)
fin = advent.get_input()

CARDVALS = {
	'A': 12 - 0,
	'K': 12 - 1,
	'Q': 12 - 2,
	'J': 12 - 3,
	'T': 12 - 4,
	'9': 12 - 5,
	'8': 12 - 6,
	'7': 12 - 7,
	'6': 12 - 8,
	'5': 12 - 9,
	'4': 12 - 10,
	'3': 12 - 11,
	'2': 12 - 12,
}

CARDVALS_JOKER = {
	'A': 12 - 0,
	'K': 12 - 1,
	'Q': 12 - 2,
	'T': 12 - 3,
	'9': 12 - 4,
	'8': 12 - 5,
	'7': 12 - 6,
	'6': 12 - 7,
	'5': 12 - 8,
	'4': 12 - 9,
	'3': 12 - 10,
	'2': 12 - 11,
	'J': 12 - 12,
}


def score(hand, vals=CARDVALS):
	counts = Counter(hand)

	# 5 of a kind
	if len(counts) == 1:
		return (7, *map(vals.get, hand))

	if len(counts) == 2:
		# 4 of a kind
		if 4 in counts.values():
			return (6, *map(vals.get, hand))
		# full house
		return (5, *map(vals.get, hand))

	if len(counts) == 3:
		# tris AAAxx
		if 3 in counts.values():
			return (4, *map(vals.get, hand))

		# 2 pair AABBx
		if 2 in counts.values():
			return (3, *map(vals.get, hand))

	# pair AAxyz
	if len(counts) == 4:
		return (2, *map(vals.get, hand))

	assert len(counts) == 5
	return (0, *map(vals.get, hand))


CARDS_NOJ = 'AKQT98765432'

def score_with_joker(hand):
	if 'J' not in hand:
		return list(score(hand, CARDVALS_JOKER))

	js = []
	for i, c in enumerate(hand):
		if c == 'J':
			js.append(i)

	hand = [*hand]
	best = [-1]

	for x in product(*([CARDS_NOJ] * len(js))):
		assert len(x) == len(js)
		for i, v in zip(js, x):
			hand[i] = v

		s = list(score(hand, CARDVALS_JOKER))
		for i in js:
			s[i + 1] = CARDVALS_JOKER['J']

		best = max(best, s)

	return best


lines = read_lines(fin); fin.seek(0, 0)
hands = {}
ans = 0

for hand, bet in map(str.split, lines):
	assert hand not in hands
	hands[hand] = int(bet)

ordered = sorted(hands.items(), key=lambda hb: score(hb[0]))

for i, (h, b) in enumerate(ordered, 1):
	ans += i * b

advent.print_answer(1, ans)

ans = 0
ordered = sorted(hands.items(), key=lambda hb: score_with_joker(hb[0]))

for i, (h, b) in enumerate(ordered, 1):
	ans += i * b

advent.print_answer(2, ans)
