#!/usr/bin/env python3

from utils import advent
from copy import deepcopy

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

def match(rules, string, rule=0, index=0):
	if index == len(string):
		return []

	rule = rules[rule]
	if type(rule) is str:
		if string[index] == rule:
			return [index + 1]
		return []

	matches = []
	for option in rule:
		sub_matches = [index]

		for sub_rule in option:
			new_matches = []
			for idx in sub_matches:
				new_matches += match(rules, string, sub_rule, idx)
			sub_matches = new_matches

		matches += sub_matches

	return matches


advent.setup(2020, 19)
fin = advent.get_input()

rules1 = parse_input(fin)
rules2 = deepcopy(rules1)
rules2[8]  = [(42,), (42, 8)]
rules2[11] = [(42, 31), (42, 11, 31)]
valid1 = 0
valid2 = 0

for msg in map(str.rstrip, fin):
	if len(msg) in match(rules1, msg):
		valid1 += 1
	if len(msg) in match(rules2, msg):
		valid2 += 1

advent.print_answer(1, valid1)
advent.print_answer(2, valid2)
