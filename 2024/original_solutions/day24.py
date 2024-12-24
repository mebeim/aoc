#!/usr/bin/env python3

from utils.all import *

advent.setup(2024, 24)
fin = advent.get_input()
data = fin.read()

g = {}
values = {}

chunk1, chunk2 = data.split('\n\n')
for line in chunk1.splitlines():
	name, num = line.split(': ')
	values[name] = int(num)

ops = {}

for line in chunk2.splitlines():
	a, b, c, d = re.findall(r'(\w+) (\w+) (\w+) -> (\w+)', line)[0]
	g[d] = [a, c]
	assert d not in ops
	ops[d] = b


def calc(var):
	if var in values:
		return values[var]

	a, b = g[var]
	op = ops[var]

	if op == 'AND':
		x = int(calc(a) and calc(b))
	elif op == 'OR':
		x = int(calc(a) or calc(b))
	elif op == 'XOR':
		x = int(calc(a) ^ calc(b))
	else:
		assert False, (var, op)

	values[var] = x
	return x

s = ''
for k in sorted(g):
	if k.startswith('z'):
		x = calc(k)
		# print(k, x)
		s += str(x)

ans1 = int(s[::-1], 2)
advent.print_answer(1, ans1)


# renames = {
# 	'nvd': 'c00',
# 	'ggk': 'c01',
# 	'gjk': 'c02',
# 	'mcf': 'c03',
# 	'grm': 'c04',
# 	'dgj': 's01',
# 	'hrp': 's03',
# }

# Solved finding these by hand with the help of the dot graph generated below
swaps = [
	('z06', 'hwk'),
	('qmd', 'tnt'),
	('z31', 'hpc'),
	('z37', 'cgr'),
]

g = {}
for line in chunk2.splitlines():
	a, b, c, d = re.findall(r'(\w+) (\w+) (\w+) -> (\w+)', line)[0]
	# a = renames.get(a,a)
	# c = renames.get(c,c)
	# d = renames.get(d,d)
	g[d] = [a, b, c]

for a, b in swaps:
	g[a], g[b] = g[b], g[a]

# Generate .dot graph to solve by hand
#
# with open('x.dot', 'w') as f:
# 	f.write('digraph {\n')
# 	f.write('node [fontname="Consolas", shape=box width=.5];\n')
# 	f.write('splines=ortho;\nrankdir="LR";\n')
#
# 	opid = 1
# 	opnames = {'XOR': '^', 'AND': '&', 'OR': '|'}
# 	opcolors = {'XOR': 'darkgreen', 'AND': 'red', 'OR': 'blue'}
# 	for v, (a, op, b) in g.items():
# 		if v.startswith('z'):
# 			f.write(f'{v} [color="purple" fontcolor="purple"];\n')
#
# 		f.write(f'op{opid} [label="{opnames[op]}" color="{opcolors[op]}"'
# 			f'fontcolor="{opcolors[op]}"];\n')
# 		f.write(f'{a} -> op{opid};\n')
# 		f.write(f'{b} -> op{opid};\n')
# 		f.write(f'op{opid} -> {v};\n')
# 		opid += 1
#
# 	f.write('}\n')

sol = sorted(swaps[0] + swaps[1] + swaps[2] + swaps[3])
ans2 = ','.join(sol)
advent.print_answer(2, ans2)
