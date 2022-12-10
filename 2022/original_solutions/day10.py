#!/usr/bin/env python3

from utils.all import *

advent.setup(2022, 10)

fin = advent.get_input()
lines = get_lines(fin)

ans = 0
cycles = 1
x = 1

for line in lines:
	if line.startswith('noop'):
		cycles += 1
	else:
		n = int(line.split()[1])
		cycles += 1

		if cycles == 20 or ((cycles - 20) % 40 == 0):
			# eprint(cycles, x, ans)
			ans += x * cycles

		cycles += 1

		x += n

	if cycles == 20 or ((cycles - 20) % 40 == 0):
		# eprint(cycles, x, ans)
		ans += cycles * x

advent.print_answer(1, ans)


ans = 0
cycles = 1
x = 1
rows = []
row = ''

for line in lines:
	if x <= (cycles % 40) < x + 3:
		row += '#'
	else:
		row += ' '

	# eprint(cycles, x)
	# eprint(row)

	if line.startswith('noop'):
		cycles += 1
	else:
		n = int(line.split()[1])
		cycles += 1

		if (cycles - 1) % 40 == 0:
			rows.append(row)
			row = ''

		if x <= (cycles % 40) < x + 3:
			row += '#'
		else:
			row += ' '

		# eprint(cycles, x)
		# eprint(row)

		cycles += 1
		x += n

	if (cycles - 1) % 40 == 0:
		rows.append(row)
		row = ''

rows.append(row)

print('Part 2:')
for r in rows:
	print(r)
