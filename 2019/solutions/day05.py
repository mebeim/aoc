#!/usr/bin/env python3

from utils import advent
from lib.intcode import IntcodeVM

advent.setup(2019, 5)
fin = advent.get_input()

program = list(map(int, fin.read().split(',')))
vm = IntcodeVM(program)
out = vm.run([1])[-1]
advent.print_answer(1, out)

out = vm.run([5])[-1]
advent.print_answer(2, out)
