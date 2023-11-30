#!/usr/bin/env python3

import sys
from collections import deque

def check(s):
	stack = deque()

	for c in s:
		if c in '([{<':
			stack.append(c.translate(TRANS_TABLE))
		elif stack.pop() != c:
			return SYNTAX_SCORE[c], 0

	score2 = 0
	while stack:
		score2 *= 5
		score2 += COMPL_SCORE[stack.pop()]

	return 0, score2

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

TRANS_TABLE  = str.maketrans('([{<', ')]}>')
SYNTAX_SCORE = {')': 3, ']': 57, '}': 1197, '>': 25137}
COMPL_SCORE  = {')': 1, ']': 2 , '}': 3   , '>': 4    }

tot_syntax = 0
autocompl_scores = []

for l in map(str.rstrip, fin):
	score1, score2 = check(l)
	tot_syntax += score1

	if score2 > 0:
		autocompl_scores.append(score2)

autocompl_scores.sort()
mid_autocompl = autocompl_scores[len(autocompl_scores) // 2]

print('Part 1:', tot_syntax)
print('Part 2:', mid_autocompl)
