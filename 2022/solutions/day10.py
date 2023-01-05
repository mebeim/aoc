#!/usr/bin/env python3

from utils import advent

advent.setup(2022, 10)

total = 0
cycle = 1
x = 1
crt = ''

with advent.get_input() as fin:
    for instr in fin:
        crt += '#' if x <= cycle % 40 < x + 3 else ' '
        cycle += 1

        if instr.startswith('addx'):
            if cycle % 40 == 20:
                total += cycle * x
            elif cycle % 40 == 1:
                crt += '\n'

            crt += '#' if x <= cycle % 40 < x + 3 else ' '
            cycle += 1
            x += int(instr[5:])

        if cycle % 40 == 20:
            total += cycle * x
        elif cycle % 40 == 1:
            crt += '\n'

advent.print_answer(1, total)
print('Part 2:', crt, sep='\n', end='')
