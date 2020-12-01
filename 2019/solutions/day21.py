#!/usr/bin/env python3

from utils import advent
from lib.intcode import intcode_oneshot

advent.setup(2019, 21)
fin = advent.get_input()
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

advent.print_answer(2, value)

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

advent.print_answer(2, value)
