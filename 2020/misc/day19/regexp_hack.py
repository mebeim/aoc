#!/usr/bin/env python3

import re

def parse_input(fin):
	rules = {}

	for line in map(str.rstrip, fin):
		if not line:
			break

		rule_id, options = line.split(': ')
		rule_id = int(rule_id)

		if '"' in options:
			rule = options[1:-1]
		else:
			rule = []
			for option in options.split('|'):
				rule.append(tuple(map(int, option.split())))

		rules[rule_id] = rule

	return rules

def build_regexp(rules, rule=0):
	rule = rules[rule]
	if type(rule) is str:
		return rule

	options = []
	for option in rule:
		option = ''.join(build_regexp(rules, r) for r in option)
		options.append(option)

	return '(' + '|'.join(options) + ')'

def build_regexp_special(rules, rule=0):
	if rule == 8:
		return '(' + build_regexp_special(rules, 42) + ')+'

	if rule == 11:
		a = build_regexp_special(rules, 42)
		b = build_regexp_special(rules, 31)

		options = []
		for n in range(1, 51):
			options.append('{a}{{{n}}}{b}{{{n}}}'.format(a=a, b=b, n=n))

		return '(' + '|'.join(options) + ')'

	rule = rules[rule]
	if type(rule) is str:
		return rule

	options = []
	for option in rule:
		option = ''.join(build_regexp_special(rules, r) for r in option)
		options.append(option)

	return '(' + '|'.join(options) + ')'


fin = open('input.txt')

rules  = parse_input(fin)
rexp1  = re.compile('^' + build_regexp(rules) + '$')
rexp2  = re.compile('^' + build_regexp_special(rules) + '$')
print(len(build_regexp_special(rules)))
valid1 = 0
valid2 = 0

for msg in map(str.rstrip, fin):
	if rexp1.match(msg):
		valid1 += 1
	if rexp2.match(msg):
		valid2 += 1

print('Part 1:', valid1)
print('Part 2:', valid2)
