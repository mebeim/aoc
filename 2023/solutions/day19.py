#!/usr/bin/env python3

import sys
from functools import partial
from math import prod

def parse_workflows(lines):
	workflows = {}

	for line in lines:
		name = line[:line.find('{')]
		rules = line[line.find('{') + 1:-1].split(',')
		rules, last = rules[:-1], rules[-1]
		rules = map(lambda r: r.split(':'), rules)
		rules = [(exp[0], exp[1], int(exp[2:]), nxt) for exp, nxt in rules]
		workflows[name] = (rules, last)

	return workflows

def parse_variables(lines):
	for line in lines:
		assignments = line[1:-1].split(',')
		assignments = map(lambda a: a.split('='), assignments)
		yield {a[0]: int(a[1]) for a in assignments}

def run(workflows, variables):
	cur = 'in'

	while cur != 'A' and cur != 'R':
		rules, last = workflows[cur]

		for varname, op, value, nxt in rules:
			var = variables[varname]
			if op == '<' and var < value or op == '>' and var > value:
				cur = nxt
				break
		else:
			cur = last

	if cur == 'A':
		return sum(variables.values())
	return 0

def count_accepted(workflows, ranges, cur='in'):
	if cur == 'A':
		return prod(hi - lo + 1 for lo, hi in ranges.values())

	if cur == 'R':
		return 0

	rules, last = workflows[cur]
	total = 0

	for var, op, value, nxt in rules:
		lo, hi = ranges[var]

		if op == '<':
			if lo < value:
				total += count_accepted(workflows, ranges | {var: (lo, value - 1)}, nxt)

			ranges[var] = (max(lo, value), hi)
		else:
			if hi > value:
				total += count_accepted(workflows, ranges | {var: (value + 1, hi)}, nxt)

			ranges[var] = (lo, min(hi, value))

	total += count_accepted(workflows, ranges, last)
	return total


# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1], 'r') if len(sys.argv) > 1 else sys.stdin

with fin:
	raw_workflows, raw_variables = fin.read().split('\n\n')

workflows = parse_workflows(raw_workflows.splitlines())
variables = parse_variables(raw_variables.splitlines())

total = sum(map(partial(run, workflows), variables))
print('Part 1:', total)

accepted = count_accepted(workflows, {v: (1, 4000) for v in 'xmas'})
print('Part 2:', accepted)
