#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 19)
fin = advent.get_input()
timer_start()

rules = {}
final = {}

for l in fin:
	l = l.strip()
	if not l:
		break

	n, l = l.split(':')
	n = int(n)

	arr = []
	if '"' in l:
		arr = l[l.find('"') + 1:l.rfind('"')]
		final[n] = True
	else:
		if '|' in l:
			l = l.split('|')
			for x in l:
				ints = tuple(map(int, x.split()))
				arr.append(ints)
		else:
			ints = tuple(map(int, l.split()))
			arr.append(ints)

		final[n] = False

	rules[n] = arr


# NOTE: I got lucky with this one. This function fails to recognize cases in
#       which both options of an or (|) are a match, stopping at the first one.
#       In such case, if the first option fails later on we report failure, even
#       though the second option could have continued matching.This is taken
#       into account by the second function.
# @selective_cache('s', 'src', 'i')
def validate(s, src, i, d):
	# log = rlog(d)
	# log('val({}, {})\n', src, i)
	if i >= len(s):
		# log('+--> {}\n', False)
		return False, -1

	if final[src]:
		# log('+--> {} {}\n', s[i] == rules[src], i + 1)
		return s[i] == rules[src], i + 1

	anyok = False
	for sub in rules[src]:
		j = i
		allok = True
		for child in sub:
			ok, j = validate(s, child, j, d + 1)
			if not ok:
				allok = False
				break

		if allok:
			anyok = True
			i = j
			break

	# log('+--> {} {}\n', anyok, i)
	return anyok, i

def validate2(s, i, src):
	assert i <= len(s)

	if i == len(s):
		return []

	if final[src]:
		if s[i] == rules[src]:
			return [i + 1]
		return []

	res = []
	for childs in rules[src]:
		sub = [i]
		for child in childs:
			ssub = []
			for j in sub:
				for k in validate2(s, j, child):
					ssub.append(k)
			sub = ssub

		res.extend(sub)

	return res


msgs = tuple(map(str.rstrip, fin))
tot = 0

for s in msgs:
	ok, i = validate(s, 0, 0, 0)
	if ok and i == len(s):
		tot += 1

advent.print_answer(1, tot)


rules[8] = [(42,), (42, 8)]
rules[11] = [(42, 31), (42, 11, 31)]

tot = 0
for s in msgs:
	if len(s) in validate2(s, 0, 0):
		tot += 1

advent.print_answer(2, tot)
