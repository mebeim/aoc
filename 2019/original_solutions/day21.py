#!/usr/bin/env python3

from utils.all import *

fin = advent.get_input()
# eprint(*fin, sep='')
timer_start()

##################################################

from lib.intcode import IntcodeVM
prog = get_ints(fin, True)
vm = IntcodeVM(prog)

def vm_write(v):
	if v > 127:
		print('>>>>>>>>>>>', v)
		sys.exit(0)
	else:
		sys.stdout.write(chr(v))

# vm.write = vm_write

# (!A+!B+!C)D
asm1 = """\
OR A T
AND B T
AND C T
NOT T T
AND D T
NOT T T
NOT T J
WALK
"""

# !AD+!BD+!CDH
# == (!A+!B)D+!CDH
# == !(AB)D + !CDH
asm2 = """\
NOT A T
NOT B J
OR T J

AND D J

NOT C T
AND D T
AND H T

OR T J
RUN
"""


asm1 = list(map(ord, asm1))
ans1 = vm.run(asm1)[-1]
advent.submit_answer(1, ans1)

asm2 = list(map(ord, asm2.replace('\n\n', '\n')))
out = vm.run(asm2)
# for v in out:
# 	if v <= 127:
# 		sys.stdout.write(chr(v))
ans2 = out[-1]
# print(ans2)
advent.submit_answer(2, ans2)
