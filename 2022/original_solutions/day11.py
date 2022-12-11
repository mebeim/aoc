#!/usr/bin/env python3

from utils.all import *

advent.setup(2022, 11)

DEBUG = 'debug' in map(str.lower, sys.argv)
if not DEBUG:
	fin = advent.get_input()
else:
	fin = io.StringIO('''\
Monkey 0:
  Starting items: 79, 98
  Operation: new = old * 19
  Test: divisible by 23
    If true: throw to monkey 2
    If false: throw to monkey 3

Monkey 1:
  Starting items: 54, 65, 75, 74
  Operation: new = old + 6
  Test: divisible by 19
    If true: throw to monkey 2
    If false: throw to monkey 0

Monkey 2:
  Starting items: 79, 60, 97
  Operation: new = old * old
  Test: divisible by 13
    If true: throw to monkey 1
    If false: throw to monkey 3

Monkey 3:
  Starting items: 74
  Operation: new = old + 3
  Test: divisible by 17
    If true: throw to monkey 0
    If false: throw to monkey 1
''')

lines = get_lines(fin)

class M:
	def __init__(s):
		s.items = None
		s.op = None
		s.opval = None
		s.test = None
		s.true = None
		s.false = None
		s.tot = 0

	def do_op(s, x):
		if s.opval is None:
			return s.op(x, x)
		return s.op(x, s.opval)

	def __repr__(s):
		return f'MONKEY {s.items}, {s.op}, {m.opval}, {s.test}, {s.true}, {s.false}, tot={s.tot}'

ms = []
from operator import add, mul

it = iter(map(str.strip, lines))
for _ in range(4 if DEBUG else 8):
	m = M()

	next(it)
	m.items = deque(map(int, re.findall(r'\d+', next(it))))
	l = next(it)
	m.op = add if '+' in l else mul

	try:
		m.opval = int(re.findall(r'\d+', l)[0])
	except IndexError:
		pass

	m.test = int(re.findall(r'\d+',next(it))[0])
	m.true = int(re.findall(r'\d+', next(it))[0])
	m.false = int(re.findall(r'\d+', next(it))[0])
	ms.append(m)

	try:
		next(it)
	except StopIteration:
		pass

# for m in ms:
# 	eprint(m)

original = deepcopy(ms)

for i in range(20):
	for mi, m in enumerate(ms):
		while m.items:
			it = m.items.popleft()
			nit = m.do_op(it) // 3

			# eprint('>', mi, 'inspects', it, 'new val:', nit)

			if nit % m.test== 0:
				# eprint('>', 'throw to', m.true)
				ms[m.true].items.append(nit)
			else:
				# eprint('>', 'throw to', m.false)
				ms[m.false].items.append(nit)

			m.tot += 1

		# eprint()
		# eprint('--- round', i + 1, '---')
		# for m in ms:
		# 	eprint(m)
		# eprint()

ms.sort(key=lambda m: m.tot, reverse=True)
ans = ms[0].tot * ms[1].tot
advent.print_answer(1, ans)


ms = original

modulus = 1
for m in ms:
	modulus *= m.test

for i in range(10000):
	for mi, m in enumerate(ms):
		while m.items:
			it = m.items.popleft()
			nit = m.do_op(it) % modulus

			if nit % m.test== 0:
				ms[m.true].items.append(nit)
			else:
				ms[m.false].items.append(nit)

			m.tot += 1

ms.sort(key=lambda m: m.tot, reverse=True)
ans = ms[0].tot * ms[1].tot
advent.print_answer(2, ans)
