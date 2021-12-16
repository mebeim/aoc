#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 8)
if 'debug' not in map(str.lower, sys.argv):
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
be cfbegad cbdgef fgaecd cgeb fdcge agebfd fecdb fabcd edb | fdgacbe cefdb cefbgd gcbe
edbfga begcd cbg gc gcadebf fbgde acbgfd abcde gfcbed gfec | fcgedb cgb dgebacf gc
fgaebd cg bdaec gdafb agbcfd gdcbef bgcad gfac gcb cdgabef | cg cg fdcagb cbg
fbegcd cbd adcefb dageb afcb bc aefdc ecdab fgdeca fcdbega | efabcd cedba gadfec cb
aecbfdg fbg gf bafeg dbefa fcge gcbea fcaegb dgceab fcbdga | gecf egdcabf bgf bfgea
fgeab ca afcebg bdacfeg cfaedg gcfdb baec bfadeg bafgc acf | gebdcfa ecba ca fadegcb
dbcfg fgd bdegcaf fgec aegbdf ecdfab fbedc dacgb gdcebf gf | cefg dcbef fcge gbcadfe
bdfegc cbegaf gecbf dfcage bdacg ed bedf ced adcbefg gebcd | ed bcgafe cdgba cbgef
egadfb cdbfeg cegd fecab cgb gbdefca cg fgcdab egfdb bfceg | gbdfcae bgc cg cgb
gcafb gcf dcaebfg ecagb gf abcdeg gaef cafbge fdbac fegbdc | fgae cfgab fg bagce
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

sigs = []
d = []
for l in lines:
	a, b = l.split('|')
	b = b.strip().split()
	sigs.append([])
	sigs[-1].append(a.split())
	sigs[-1].append(b)

	ou = []
	for s in b:
		ou.append((''.join(sorted(list(s))), len(s)))

	d.append(ou)

count = defaultdict(int)

for s in d:
	num = 0
	for ss, lss in s:
		count[lss] += 1

ans = count[7]
ans += count[2]
ans += count[4]
ans += count[3]


advent.print_answer(1, ans)
# wait('Submit? ')
# advent.submit_answer(1, ans)

ssigs = []

for sig, out in sigs:
	a = list(map(lambda x: ''.join(sorted(x)), sig))
	b = list(map(lambda x: ''.join(sorted(x)), out))
	ssigs.append((a, b))


# dump_iterable(ssigs)

def incl(a, b):
	return all(ca in b for ca in a)

def nincl(a, b):
	return sum(ca in b for ca in a)

ans = 0
for sig, out in ssigs:
	# print(sig, out)

	mapping = {}

	for s in sig:
		if len(s) == 7:
			mapping[s] = 8
		elif len(s) == 2:
			mapping[s] = 1
		elif len(s) == 4:
			mapping[s] = 4
		elif len(s) == 3:
			mapping[s] = 7
		elif len(s) == 5: # 2 3 5
			pass
		elif len(s) == 6: # 0 6 9
			pass

	revmap = {v: k for k, v in mapping.items()}

	for s in sig:
		if len(s) == 7: # 8
			pass
		elif len(s) == 2: # 1
			pass
		elif len(s) == 4: # 4
			pass
		elif len(s) == 3: # 7
			pass
		elif len(s) == 5: # 2 3 5
			if s in mapping:
				continue

			if incl(revmap[1], s):
				mapping[s] = 3
				revmap[3] = s
			elif nincl(revmap[4], s) == 2:
				mapping[s] = 2
				revmap[2] = s
			else:
				mapping[s] = 5
				revmap[s] = s
		elif len(s) == 6: # 0 6 9
			if s in mapping:
				continue

			if incl(revmap[1], s): # 0 9
				if incl(revmap[4], s):
					mapping[s] = 9
					revmap[9] = s
				else:
					mapping[s] = 0
					revmap[0] = s
			else:
				mapping[s] = 6
				revmap[6] = s

	# dump_dict(mapping)
	num = 0
	for s in out:
		num *= 10
		num += mapping[s]
	ans += num
	# print(num)

# print(ans)

advent.print_answer(2, ans)
# wait('Submit? ')
# advent.submit_answer(2, ans)
