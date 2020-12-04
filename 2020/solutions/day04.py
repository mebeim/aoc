#!/usr/bin/env python3

from utils import advent

def check_height(v):
	if v.endswith('cm'):
		return 150 <= int(v[:-2]) <= 193
	if v.endswith('in'):
		return 59 <= int(v[:-2]) <= 76
	return False

checks = {
	'byr': lambda v: 1920 <= int(v) <= 2002,
	'iyr': lambda v: 2010 <= int(v) <= 2020,
	'eyr': lambda v: 2020 <= int(v) <= 2030,
	'pid': lambda v: len(v) == 9 and all(c.isdigit() for c in v),
	'hcl': lambda v: len(v) == 7 and all(c.isdigit() or c in 'abcdef' for c in v[1:]),
	'ecl': lambda v: v in ('amb', 'blu', 'brn', 'gry', 'grn', 'hzl', 'oth'),
	'cid': lambda v: True,
	'hgt': check_height
}

KEYS = ('byr:', 'iyr:', 'eyr:', 'hgt:', 'hcl:', 'ecl:', 'pid:')


advent.setup(2020, 4)
fin = advent.get_input()

passports = fin.read().split('\n\n')
n_valid1 = 0
n_valid2 = 0

for raw in passports:
	if all(k in raw for k in KEYS):
		n_valid1 += 1
		passport = (field.split(':') for field in raw.split())

		if all(checks[k](v) for k, v in passport):
			n_valid2 += 1

advent.print_answer(1, n_valid1)
advent.print_answer(2, n_valid2)
