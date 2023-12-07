#!/usr/bin/env python3

import sys
from math import prod
from collections import Counter

def strength(hand):
	count = Counter(hand).values()
	return sorted(count, reverse=True), hand


def strength_with_joker(hand):
	if hand == '00000':
		return [5], hand

	counts = Counter(hand)
	jokers = counts.pop('0', 0)
	freqs  = sorted(counts.values(), reverse=True)
	freqs[0] += jokers

	return freqs, hand


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

tbl     = str.maketrans('TJQKA', 'ABCDE')
bets    = {hand.translate(tbl): int(bet) for hand, bet in map(str.split, fin)}
ordered = map(bets.get, sorted(bets, key=strength))
total   = sum(map(prod, enumerate(ordered, 1)))

print('Part 1:', total)


bets    = {hand.replace('B', '0'): bet for hand, bet in bets.items()}
ordered = map(bets.get, sorted(bets, key=strength_with_joker))
total   = sum(map(prod, enumerate(ordered, 1)))

print('Part 2:', total)
