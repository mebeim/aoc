#!/usr/bin/env python3

from utils.all import *

advent.setup(2020, 4)
fin = advent.get_input()

# import io
# fin = io.StringIO('''eyr:1972 cid:100
# hcl:#18171d ecl:amb hgt:170 pid:186cm iyr:2018 byr:1926

# iyr:2019
# hcl:#602927 eyr:1967 hgt:170cm
# ecl:grn pid:012533040 byr:1946

# hcl:dab227 iyr:2012
# ecl:brn hgt:182cm pid:021572410 eyr:2020 byr:1992 cid:277

# hgt:59cm ecl:zzz
# eyr:2038 hcl:74454a iyr:2023
# pid:3556412378 byr:2007''')

timer_start()
data = fin.read().split('\n\n')

fields = [
	'byr',
	'iyr',
	'eyr',
	'hgt',
	'hcl',
	'ecl',
	'pid',
	# 'cid'
]

ok = 0
for x in data:
	if all((f + ':') in x for f in fields):
		ok += 1

advent.print_answer(1, ok)

# byr (Birth Year) - four digits; at least 1920 and at most 2002.
# iyr (Issue Year) - four digits; at least 2010 and at most 2020.
# eyr (Expiration Year) - four digits; at least 2020 and at most 2030.
# hgt (Height) - a number followed by either cm or in:
# If cm, the number must be at least 150 and at most 193.
# If in, the number must be at least 59 and at most 76.
# hcl (Hair Color) - a # followed by exactly six characters 0-9 or a-f.
# ecl (Eye Color) - exactly one of: amb blu brn gry grn hzl oth.
# pid (Passport ID) - a nine-digit number, including leading zeroes.
# cid (Country ID) - ignored, missing or not.

def g(x):
	m = re.findall(r'(\d+)(cm|in)', x)

	if not m:
		return False

	h, z = m[0]
	h = int(h)
	if z == 'cm':
		return 150 <= h <= 193
	else:
		return 59 <= h <= 76

f = {
	'byr': lambda x: 1920 <= int(x) <= 2020,
	'iyr': lambda x: 2010 <= int(x) <= 2020,
	'eyr': lambda x: 2020 <= int(x) <= 2030,
	'hgt': lambda x: g(x),
	'hcl': lambda x: bool(re.match(r'#[0-9a-f]{6}', x)),
	'ecl': lambda x: x in ('amb', 'blu', 'brn', 'gry', 'grn', 'hzl', 'oth'),
	'pid': lambda x: bool(re.match(r'^\d{9}$', x)),
	'cid': lambda x: True
}

ok = 0
for nn, x in enumerate(data):
	x = x.replace('\n', ' ')
	x = dict(map(lambda y: y.split(':'), x.split()))

	valid = True
	for k, func in f.items():
		if k != 'cid' and k not in x:
			valid = False
			break

		val = x.get(k)

		try:
			res = func(val)
			if not func(val):
				valid = False
				break
		except:
			valid = False
			continue

	if valid:
		ok += 1
		# print(nn)

	# eprint(nn, x)

# 193 not right
# 195 not right
advent.print_answer(2, ok)
