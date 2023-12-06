#!/usr/bin/env python3
#
# Arithmetical solution using complex numbers as coordinates.
#

import sys

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

with fin:
	commands = tuple(map(lambda l: (l[0], int(l[1:])), fin))

# Deltas to apply to move forward in a specific direction.
deltas = {
	'N':  0 + 1j,
	'S':  0 - 1j,
	'E':  1 + 0j,
	'W': -1 + 0j,
}

pos   = 0 + 0j
delta = deltas['E']

for cmd, n in commands:
	if cmd == 'F':
		pos += delta * n
	elif cmd == 'L':
		delta *= 1j ** (n // 90)
	elif cmd == 'R':
		delta *= 1j ** (-n // 90)
	else:
		pos += deltas[cmd] * n

dist = int(abs(pos.real) + abs(pos.imag))
print('Part 1:', dist)


pos = 0 + 0j
way = 10 + 1j

for cmd, n in commands:
	if cmd == 'F':
		pos += way * n
	elif cmd == 'L':
		way *= 1j ** (n // 90)
	elif cmd == 'R':
		way *= 1j ** (-n // 90)
	else:
		way += deltas[cmd] * n

dist = int(abs(pos.real) + abs(pos.imag))
print('Part 2:', dist)
