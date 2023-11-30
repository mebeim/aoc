#!/usr/bin/env python3

import sys

def into_matrix(raw):
	lines = raw.strip().splitlines()
	return list(list(map(int, l.split())) for l in lines)

def check_win(card, row, c):
	if sum(x == -1 for x in row) == 5:
		return True
	if sum(r[c] == -1 for r in card) == 5:
		return True
	return False

def mark(card, number):
	for r, row in enumerate(card):
		for c, cell in enumerate(row):
			if cell == number:
				card[r][c] = -1
				return check_win(card, row, c)
	return False

def winner_score(card, last_number):
	unmarked_tot = sum(sum(filter(lambda x: x != -1, row)) for row in card)
	return unmarked_tot * last_number


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

drawn   = map(int, fin.readline().split(','))
cards   = list(map(into_matrix, fin.read().split('\n\n')))
n_cards = len(cards)
n_won   = 0

for number in drawn:
	for i, card in enumerate(cards):
		if card is None:
			continue

		if mark(card, number):
			n_won += 1

			if n_won == 1:
				first_winner_score = winner_score(card, number)
			elif n_won == n_cards:
				last_winner_score = winner_score(card, number)

			cards[i] = None

print('Part 1:', first_winner_score)
print('Part 2:', last_winner_score)
