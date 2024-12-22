#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 22)
DEBUG = 'debug' in map(str.lower, sys.argv)
# DEBUG = True
fin = advent.get_input() if not DEBUG else io.StringIO('''\
1
2
3
2024
''')

data = fin.read()
ints = extract_ints(data)


def do(x):
	for _ in range(2000):
		x = ((x << 6) ^ x) & 16777215
		x = ((x >> 5) ^ x) & 16777215
		x = ((x << 11) ^ x) & 16777215
	return x

def seq(x):
	yield x % 10
	for _ in range(2000):
		x = ((x << 6) ^ x) & 16777215
		x = ((x >> 5) ^ x) & 16777215
		x = ((x << 11) ^ x) & 16777215
		yield x % 10

sequences = list(list(seq(x)) for x in ints)
differences = []

for s in sequences:
	d = []
	for i in range(len(s) - 1):
		d.append(s[i + 1] - s[i])
	differences.append(tuple(d))

ans1 = sum(map(do, ints))
advent.print_answer(1, ans1)


def brute_task(a):
	seqs, diffss, maps, guess = a
	total = 0

	g = guess[0]
	for seq, diffs, m in zip(seqs, diffss, maps):
		for i in m[g]:
			if diffs[i:i + 4] == guess:
				total += seq[i + 4]
				break

	return total

def brute(seqs, diffss, maps):
	import tqdm
	from multiprocessing import Pool

	args = list((seqs, diffss, maps, p) for p in product(range(-9, 10), repeat=4))
	best = 0

	with Pool(20) as p:
		it = p.imap_unordered(brute_task, args, chunksize=200)
		for x in tqdm.tqdm(it, total=len(args)):
			best = max(best, x)

	return best

maps = []
for diffs in differences:
	m = defaultdict(list)

	for n in range(-9, 10):
		for i, d in enumerate(diffs):
			if d == n:
				m[n].append(i)

	maps.append(m)

ans2 = brute(sequences, differences, maps)
advent.print_answer(2, ans2)
