#!/usr/bin/env python3

from utils.all import *

def check_ok(l, nums):
	l = ''.join(l)
	l = tuple(map(len, filter(None, l.split('.'))))
	return l == nums

# @log_calls_recursive()
@selective_cache('lengths', 'i', 'curlen')
def search(l, lengths, i, curlen):
	if i == len(l):
		return not lengths and curlen == 0 or len(lengths) == 1 and lengths[0] == curlen

	total = 0

	# broken
	if l[i] == '#':
		# cur chunk is 1 longer, advance
		total += search(l, lengths, i + 1, curlen + 1)

	# not broken
	elif l[i] in '.':
		# cannot have chunk here, start new chunk later
		if not curlen:
			# we had no previous chunk
			total += search(l, lengths, i + 1, 0)
		elif lengths and lengths[0] == curlen:
			# previous chunk completed
			total += search(l, lengths[1:], i + 1, 0)

	# unknown
	else:
		# put '#' here
		total += search(l, lengths, i + 1, curlen + 1)

		# put '.' here, start new chunk
		if not curlen:
			# we had no previous chunk
			total += search(l, lengths, i + 1, 0)
		elif lengths and lengths[0] == curlen:
			# previous chunk completed
			total += search(l, lengths[1:], i + 1, 0)

	return total


advent.setup(2023, 12)
fin = advent.get_input()

lines = read_lines(fin)
ans1 = ans2 = 0

for l in lines:
	l, nums = l.split()
	nums = extract_ints(nums, container=tuple)

	indices = []
	for i, c in enumerate(l):
		if c == '?':
			indices.append(i)

	# very slow bruteforce, might wanna use pypy3
	for replacement in product('.#', repeat=len(indices)):
		assert len(replacement) == len(indices)

		x = list(l)
		for i, r in zip(indices, replacement):
			x[i] = r

		ans1 += check_ok(x, nums)

	l = '?'.join([l] * 5)
	nums *= 5

	ans2 += search(l, nums, 0, 0)
	search.cache_clear()

advent.print_answer(1, ans1)
advent.print_answer(2, ans2)
