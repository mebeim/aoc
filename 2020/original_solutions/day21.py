#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 21)
fin = advent.get_input()
TESTPLZ = any(a.lower() == 'test' for a in sys.argv[1:])
ftest = io.StringIO('''\
mxmxvkd kfcds sqjhc nhms (contains dairy, fish)
trh fvjkl sbzzf mxmxvkd (contains dairy)
sqjhc fvjkl (contains soy)
sqjhc mxmxvkd sbzzf (contains fish)
''')

if TESTPLZ:
	fin = ftest

timer_start()

lines = get_lines(fin)
recipes = []
can_contain = defaultdict(set)
recipes_with_aller = defaultdict(set)
i = 0

for l in lines:
	l = l.rstrip()
	l = l.rstrip(')')
	l = l.split(' (contains ')

	a, b = l[0].split(), l[1].split(', ')
	recipes.append((a, b))

	for bb in b:
		for aa in a:
			can_contain[aa].add(bb)
			recipes_with_aller[bb].add(i)
	i += 1

# dump_dict(recipes_with_aller)

for ingrs, allers in recipes:
	for i in ingrs:
		for a in allers:
			if a in can_contain[i]:
				for idx in recipes_with_aller[a]:
					if i not in recipes[idx][0]:
						can_contain[i].remove(a)
						break

ans = 0
for k, v in can_contain.items():
	if len(v) == 0:
		for ingrs, _ in recipes:
			if k in ingrs:
				ans += 1

advent.print_answer(1, ans)

# dump_dict(can_contain)

todel = []
for k, v in can_contain.items():
	if not v:
		todel.append(k)

for k in todel:
	del can_contain[k]

final = []
while can_contain:
	for k, v in can_contain.items():
		if len(v) == 1:
			match = k
			break

	a = can_contain[match].pop()
	final.append((a, k))
	del can_contain[match]

	for k, v in can_contain.items():
		if a in v:
			v.remove(a)

ans2 = ','.join(map(itemgetter(1), sorted(final)))
# eprint(','.join(map(itemgetter(0), sorted(final))))

advent.print_answer(2, ans2)
