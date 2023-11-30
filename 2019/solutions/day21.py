#!/usr/bin/env python3

import sys
from lib.intcode import intcode_oneshot

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin
program = list(map(int, fin.read().split(',')))

# (!A | !B | !C) & D
# == !(A & B & C) & D
springscript = """\
NOT A J
NOT J J
AND B J
AND C J
NOT J J
AND D J
WALK
"""

inp = list(map(ord, springscript))
for value in intcode_oneshot(program, inp):
	continue

print('Part 2:', value)

# (!A & D) | (!B & D) | (!C & D & H)
# == (!A | !B | (!C & H)) & D
springscript = """\
NOT C J
AND H J
NOT B T
OR T J
NOT A T
OR T J
AND D J
RUN
"""

inp = list(map(ord, springscript))
for value in intcode_oneshot(program, inp):
	continue

print('Part 2:', value)
