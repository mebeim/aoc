#!/usr/bin/env python3

from utils.all import *

poly = 'FSHBKOOPCFSFKONFNFBB'

rules = dict([
	('FO', 'K'),	('FF', 'H'),	('SN', 'C'),	('CC', 'S'),	('BB', 'V'),	('FK', 'H'),	('PC', 'P'),	('PH', 'N'),	('OB', 'O'),	('PV', 'C'),	('BH', 'B'),	('HO', 'C'),	('VF', 'H'),	('HB', 'O'),	('VO', 'N'),	('HK', 'N'),	('OF', 'V'),	('PF', 'C'),	('KS', 'H'),	('KV', 'F'),	('PO', 'B'),	('BF', 'P'),	('OO', 'B'),	('PS', 'S'),	('KC', 'P'),	('BV', 'K'),	('OC', 'B'),	('SH', 'C'),	('SF', 'P'),	('NH', 'C'),	('BS', 'C'),	('VH', 'F'),	('CH', 'S'),	('BC', 'B'),	('ON', 'K'),	('FH', 'O'),	('HN', 'O'),	('HS', 'C'),	('KK', 'V'),	('OK', 'K'),	('VC', 'H'),	('HV', 'F'),	('FS', 'H'),	('OV', 'P'),	('HF', 'F'),	('FB', 'O'),	('CK', 'O'),	('HP', 'C'),	('NN', 'V'),	('PP', 'F'),	('FC', 'O'),	('SK', 'N'),	('FN', 'K'),	('HH', 'F'),	('BP', 'O'),	('CP', 'K'),	('VV', 'S'),	('BO', 'N'),	('KN', 'S'),	('SB', 'B'),	('SC', 'H'),	('OS', 'S'),	('CF', 'K'),	('OP', 'P'),	('CO', 'C'),	('VK', 'C'),	('NB', 'K'),	('PB', 'S'),	('FV', 'B'),	('CS', 'C'),	('HC', 'P'),	('PK', 'V'),	('BK', 'P'),	('KF', 'V'),	('NS', 'P'),	('SO', 'C'),	('CV', 'P'),	('NP', 'V'),	('VB', 'F'),	('KO', 'C'),	('KP', 'F'),	('KH', 'N'),	('VN', 'S'),	('NO', 'P'),	('NF', 'K'),	('CB', 'H'),	('VS', 'V'),	('NK', 'N'),	('KB', 'C'),	('SV', 'F'),	('NC', 'H'),	('VP', 'K'),	('PN', 'H'),	('OH', 'K'),	('CN', 'N'),	('BN', 'F'),	('NV', 'K'),	('SP', 'S'),	('SS', 'K'),	('FP', 'S'),])

if 'debug' in sys.argv:
	poly = 'NNCB'

	rules = dict([
	('CH', 'B'),
	('HH', 'N'),
	('CB', 'H'),
	('NH', 'C'),
	('HB', 'C'),
	('HC', 'B'),
	('HN', 'C'),
	('NN', 'C'),
	('BH', 'H'),
	('NC', 'B'),
	('NB', 'B'),
	('BN', 'B'),
	('BB', 'N'),
	('BC', 'B'),
	('CC', 'N'),
	('CN', 'C'), ])


class LL:
	__slots__ = ('v', 'next')
	def __init__(self, v):
		self.v = v
		self.next = None

l = LL(poly[0])
cur = l
for letter in poly[1:]:
	cur.next = LL(letter)
	cur = cur.next

def dump(l):
	cur = l
	n = 0
	while cur:
		eprint(cur.v, end='')
		cur = cur.next
		n += 1
	eprint(n)

for step in range(10):
	# print(step)
	cur = l
	while cur.next:
		n = cur.next
		ab = cur.v + n.v

		if ab in rules:
			cur.next = LL(rules[ab])
			cur.next.next = n

			cur = n
		else:
			cur = cur.next

	# dump(l)


def count(l):
	c = defaultdict(int)
	cur = l
	while cur:
		c[cur.v] += 1
		cur = cur.next

	return c

c = count(l)
# eprint(c)
l = min(c.values())
m = max(c.values())

ans = m - l

advent.print_answer(1, ans)
# wait('Submit? ')
# advent.submit_answer(1, ans)

counts = defaultdict(int)

for a, b in zip(poly, poly[1:]):
	counts[a + b] += 1

newrules = {}
for ab, c in rules.items():
	newrules[ab] = (ab[0] + c, c + ab[1])

for sss in range(40):
	# eprint(sss, counts)
	new = defaultdict(int)

	for ab in counts:
		a, b = ab
		c = newrules.get(ab)
		# eprint('>>', ab, c)

		if c:
			x, y = c
			n = counts[ab]
			new[x] += n
			new[y] += n
		else:
			new[ab] = counts[ab]

	counts = new

# eprint(sss + 1, counts)

singlecounts = defaultdict(int)
for (a, _), n in counts.items():
	singlecounts[a] += n

singlecounts[poly[-1]] += 1

ans = max(singlecounts.values()) - min(singlecounts.values())

# assert ans == 2188189693529, f'actually {ans}'

advent.print_answer(2, ans)
wait('Submit? ')
advent.submit_answer(2, ans)
