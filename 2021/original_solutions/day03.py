#!/usr/bin/env python3

from utils.all import *

advent.setup(2021, 3)
if 'debug' not in map(str.lower, sys.argv):
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
00100
11110
10110
10111
10101
01111
00111
11100
10000
11001
00010
01010
''')

# eprint(*fin, sep='', end='----- end of input -----\n\n'); fin.seek(0, 0)

ans = 0
try: lines = get_lines(fin); fin.seek(0, 0)
except: pass

occur = defaultdict(int)

for i, l in enumerate(lines):
	bits = list(map(int, l.strip()))
	print(bits)

	for col, bit in enumerate(bits):
		occur[col, bit] += 1

mostcom = {}
leastcom = {}
for col in range(len(bits)):
	if occur[col, 1] >= occur[col, 0]:
		mostcom[col] = 1
		leastcom[col] = 0
	else:
		mostcom[col] = 0
		leastcom[col] = 1


gamma = 0
eps = 0
for col in range(len(bits)):
	gamma = gamma << 1
	eps = eps << 1
	gamma += mostcom[col]
	eps += leastcom[col]

print(gamma, eps)
for r, row in enumerate(mat):
	for c, cell in enumerate(row):
		pass

ans = gamma * eps


advent.print_answer(1, ans)
# wait('Submit? ')
# advent.submit_answer(1, ans)

col = 0
filtered = set(map(lambda x: tuple(map(int, x)), lines))

while len(filtered) != 1:
	todel = set()

	for n in filtered:
		if n[col] != mostcom[col]:
			todel.add(n)

	filtered -= todel
	a = filtered.pop()
	nbits = len(a)
	filtered.add(a)

	occur = defaultdict(int)

	for bits in filtered:
		for c, bit in enumerate(bits):
			occur[c, bit] += 1

	mostcom = {}
	leastcom = {}
	for c in range(nbits):
		if occur[c, 1] >= occur[c, 0]:
			mostcom[c] = 1
			leastcom[c] = 0
		else:
			mostcom[c] = 0
			leastcom[c] = 1

	col += 1
	if len(filtered) == 0:
		break

print(filtered)
x = int(''.join(map(str, filtered.pop())), 2)
print('>>', x)

col = 0
filtered = set(map(lambda x: tuple(map(int, x)), lines))

while len(filtered) != 1:
	todel = set()

	for n in filtered:
		if n[col] != leastcom[col]:
			todel.add(n)

	filtered -= todel
	a = filtered.pop()
	nbits = len(a)
	filtered.add(a)

	occur = defaultdict(int)

	for bits in filtered:
		for c, bit in enumerate(bits):
			occur[c, bit] += 1

	mostcom = {}
	leastcom = {}
	for c in range(nbits):
		if occur[c, 1] >= occur[c, 0]:
			mostcom[c] = 1
			leastcom[c] = 0
		else:
			mostcom[c] = 0
			leastcom[c] = 1

	col += 1
	if len(filtered) == 0:
		break

y = int(''.join(map(str, filtered.pop())), 2)
print('>>', y)

ans = x * y

advent.print_answer(2, ans)
# wait('Submit? ')
advent.submit_answer(2, ans)
