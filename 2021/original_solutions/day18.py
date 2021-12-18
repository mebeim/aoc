#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 18)
DEBUG = 'debug' in map(str.lower, sys.argv)
if not DEBUG:
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
[[[0,[4,5]],[0,0]],[[[4,5],[2,6]],[9,5]]]
[7,[[[3,7],[4,3]],[[6,3],[8,8]]]]
[[2,[[0,8],[3,4]]],[[[6,7],1],[7,[1,6]]]]
[[[[2,4],7],[6,[0,5]]],[[[6,8],[2,8]],[[2,1],[4,5]]]]
[7,[5,[[3,8],[1,4]]]]
[[2,[2,2]],[8,[8,1]]]
[2,9]
[1,[[[9,3],9],[[9,0],[0,7]]]]
[[[5,[7,4]],7],1]
[[[[4,2],2],6],[8,7]]
''')

# eprint(*fin, sep='', end='----- end of input -----\n\n'); fin.seek(0, 0)
timer_start()

def replace_num(s, start, end, newnum):
	return s[:start] + str(newnum) + s[end:]

def add_num(s, start, end, toadd):
	other = int(s[start:end])
	return replace_num(s, start, end, other + toadd)

def explode(s):
	depth = 0

	for i, c in enumerate(s):
		if c == '[':
			depth += 1

			if depth == 5:
				for j in range(i + 1, len(s)):
					if not s[j].isdigit():
						# print(i, j, s[j], s[i:])
						assert s[j] == ','
						assert s[j + 1].isdigit()
						break

				for k in range(j + 1, len(s)):
					if not s[k].isdigit():
						# print(i, j, s[j], s[i:])
						assert s[k] == ']'
						break

				a = int(s[i + 1:j])
				b = int(s[j + 1:k])
				# print(a, b)

				# replace pair with 0
				# eprint('      ', s)
				s = replace_num(s, i, k + 1, 0)
				# eprint('ab->0 ', s)

				# go left
				for j in range(i - 1, -1, -1):
					if s[j].isdigit():
						break

				if j != 0: # left number found
					for k in range(j - 1, -1, -1):
						if not s[k].isdigit():
							break

					# eprint(k, j, s[k:j])
					s = add_num(s, k + 1, j + 1, a)
					# eprint('left+ ', s)

				# go right
				for j in range(i + 2, len(s)):
					if s[j].isdigit():
						break

				if j != len(s) - 1: # right number found
					for k in range(j + 1, len(s)):
						if not s[k].isdigit():
							break

					# eprint(j, k, s[j:k])
					s = add_num(s, j, k, b)
					# eprint('right+', s)

				return s, True

		elif c == ']':
			depth -= 1

	return s, False

def split(s):
	for i, c in enumerate(s):
		if not c.isdigit():
			continue

		for j in range(i + 1, len(s)):
			if not s[j].isdigit():
				break

		n = int(s[i:j])
		if n >= 10:
			a = n // 2
			b = n - a

			s = replace_num(s, i, j, f'[{a},{b}]')
			return s, True

	return s, False

def redux(s):
	ok = True
	while ok:
		s, ok = explode(s)
		if ok:
			# eprint('e', s)
			continue

		s, ok = split(s)
		# if ok:
			# eprint('s', s)

	return s

def magnitude(lst):
	if type(lst) is int:
		return lst

	left, right = lst
	return 3 * magnitude(left) + 2 * magnitude(right)


res = next(fin).rstrip()

for line in map(str.rstrip, fin):
	# eprint(line)
	res = f'[{res},{line}]'
	# eprint(' ', res)

	res = redux(res)

	# break
# explode('[[[[[9,8],1],2],3],4]')

ans = magnitude(eval(res))

advent.print_answer(1, ans)
# wait('Submit? ')
# advent.submit_answer(1, ans)



fin.seek(0, 0)
lsts = list(map(str.rstrip, fin))

best = 0
for a, b in product(lsts, lsts):
	if a is b:
		continue

	m = magnitude(eval(redux(f'[{a},{b}]')))
	if m > best:
		best = m

	m = magnitude(eval(redux(f'[{b},{a}]')))
	if m > best:
		best = m

ans = best

advent.print_answer(2, ans)
# wait('Submit? ')
# advent.submit_answer(2, ans)
