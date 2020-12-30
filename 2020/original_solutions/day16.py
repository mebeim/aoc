#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 16)
fin = advent.get_input()
TESTPLZ = any(a.lower() == 'test' for a in sys.argv[1:])
ftest = io.StringIO('''\

''')

if TESTPLZ:
	fin = ftest

# eprint(*fin, sep=''); fin.seek(0, 0)
timer_start()

if not TESTPLZ:
	lines=get_lines(fin)
	i = 0
	start = None
	for i, l in enumerate(lines):
		if l.startswith('nearby'):
			start = i + 1
	lines = lines[start:]

	fields = {
		'departure location': (range(42, 322 + 1), range(347, 954 + 1)),
		'departure station' : (range(49, 533 + 1), range(555, 966 + 1)),
		'departure platform': (range(28,  86 + 1), range(101, 974 + 1)),
		'departure track'   : (range(50, 150 + 1), range(156, 950 + 1)),
		'departure date'    : (range(30, 117 + 1), range(129, 957 + 1)),
		'departure time'    : (range(31, 660 + 1), range(678, 951 + 1)),
		'arrival location'  : (range(26, 482 + 1), range(504, 959 + 1)),
		'arrival station'   : (range(29, 207 + 1), range(220, 971 + 1)),
		'arrival platform'  : (range(28, 805 + 1), range(829, 964 + 1)),
		'arrival track'     : (range(48, 377 + 1), range(401, 964 + 1)),
		'class'             : (range(28, 138 + 1), range(145, 959 + 1)),
		'duration'          : (range(33, 182 + 1), range(205, 966 + 1)),
		'price'             : (range(25, 437 + 1), range(449, 962 + 1)),
		'route'             : (range(41, 403 + 1), range(428, 968 + 1)),
		'row'               : (range(33, 867 + 1), range(880, 960 + 1)),
		'seat'              : (range(40, 921 + 1), range(930, 955 + 1)),
		'train'             : (range(47, 721 + 1), range(732, 955 + 1)),
		'type'              : (range(33, 243 + 1), range(265, 964 + 1)),
		'wagon'             : (range(31, 756 + 1), range(768, 973 + 1)),
		'zone'              : (range(50, 690 + 1), range(713, 967 + 1)),
	}

def find_invalid(tkt):
	for v in tkt:
		allwrong = True
		for r1, r2 in fields.values():
			if v in r1 or v in r2:
				allwrong = False
		if allwrong:
			yield v

ans = 0
for l in lines:
	tkt = map(int, l.split(','))

	for v in find_invalid(tkt):
		ans += v

advent.print_answer(1, ans)

def is_invalid(tkt):
	for v in tkt:
		allwrong = True
		for r1, r2 in fields.values():
			if v in r1 or v in r2:
				allwrong = False
				break
		if allwrong:
			return True
	return False

def filter_idx(tkt):
	for i, v in enumerate(tkt):
		for f, (r1, r2) in fields.items():
			# eprint(f, v, r1, r2)
			if v not in r1 and v not in r2:
				# eprint('invalid', f.ljust(25), f'{v} not in {r1.start}-{r1.stop} {r2.start}-{r2.stop}', ' idx', i)
				if i in possible[f]:
					possible[f].remove(i)

if TESTPLZ:
	fields = {
	'class': (range(0, 1+1), range(4,19+1)),
	'row': (range(0, 5+1), range(8,19+1)),
	'seat': (range(0, 13+1), range(16,19+1)),
	}

	myticket = [11,12,13]
	lines = '''\
11,12,13
3,9,18
15,1,5
5,14,9
'''.splitlines()
else:
	myticket = [67,107,59,79,53,131,61,101,71,73,137,109,157,113,173,103,83,167,149,163]
	lines.append('67,107,59,79,53,131,61,101,71,73,137,109,157,113,173,103,83,167,149,163')

possible = {f: set(range(len(fields))) for f in fields}

for l in lines:
	if l.startswith('debugstop'):
		break
	tkt = list(map(int, l.split(',')))
	# eprint(tkt, 'INVALID' if is_invalid(tkt) else 'ok')

	if is_invalid(tkt):
		continue

	filter_idx(tkt)

# eprint('-'*50)
# for k, v in possible.items():
# 	eprint(k.ljust(25), len(v), v)

assert all(possible.values()), 'filtered too many'

# simplify
found = set()
while any(len(s) > 1 for s in possible.values()):
	for s in possible.values():
		if len(s) == 1:
			v = next(iter(s))
			if v not in found:
				found.add(v)
				ss = s
				break

	for s in possible.values():
		if s is not ss:
			if v in s:
				s.remove(v)

	assert all(possible.values()), 'filtered too many 2'

# eprint('-'*50)
# for k, v in possible.items():
# 	eprint(k.ljust(25), len(v), v)

ans = 1
for f, i in possible.items():
	i = i.pop()
	if f.startswith('departure'):
		ans *= myticket[i]

advent.print_answer(2, ans)
# advent.submit_answer(2, ans2)
