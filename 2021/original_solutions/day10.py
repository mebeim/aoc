#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 10)
if 'debug' not in map(str.lower, sys.argv):
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
[({(<(())[]>[[{[]{<()<>>
[(()[<>])]({[<{<<[]>>(
{([(<{}[<>[]}>{[]{[(<()>
(((({<>}<{<{<>}{[]{[]{}
[[<[([]))<([[{}[[()]]]
[{[{({}]{}}([{[{{{}}([]
{<[[]]>}<{[{[{[]{()[[[]
[<(<(<(<{}))><([]([]()
<{([([[(<>()){}]>(<<{{
<{([{{}}[<[[[<>{}]]]>[]]
''')

eprint(*fin, sep='', end='----- end of input -----\n\n'); fin.seek(0, 0)
timer_start()

ans = 0
try: ints = get_ints(fin, True); fin.seek(0, 0)
except: pass
try: lines = get_lines(fin); fin.seek(0, 0)
except: pass
try: mat = get_char_matrix(fin, rstrip=False, lstrip=False); fin.seek(0, 0)
except: pass


scores = {
	')': 3,
	']': 57,
	'}': 1197,
	'>': 25137,
}

scores2 = {
	')': 1,
	']': 2,
	'}': 3,
	'>': 4,
}

revmap = {
	'(': ')',
	'[': ']',
	'{': '}',
	'<': '>',
}

def check(s):
	stack = deque()
	for c in s:
		if c in '([{<':
			stack.append(revmap[c])
		else:
			x = stack.pop()
			if x != c:
				return scores[c]
	return 0

ans = 0
for s in lines:
	s = s.strip()
	ans += check(s)


advent.print_answer(1, ans)
# wait('Submit? ')
# advent.submit_answer(1, ans)

def check2(s):
	stack = deque()
	for c in s:
		if c in '([{<':
			stack.append(revmap[c])
		else:
			x = stack.pop()
			if x != c:
				return 0 # bug, not incomplete

	score = 0
	# if stack:
		# print(stack)
	while stack:
		c = stack.pop()
		# print(c, scores2[c])
		score *= 5
		score += scores2[c]

	return score


scores = []
for s in lines:
	s = s.strip()
	ss = check2(s)
	# print(ss)
	if ss > 0:
		scores.append(ss)

	# if ss > 0:
		# print(s)

scores.sort()
# print(scores)
ans = scores[len(scores)//2]


advent.print_answer(2, ans)
wait('Submit? ')
advent.submit_answer(2, ans)
