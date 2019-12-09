#!/usr/bin/env python3

import advent
from lib.intcode import IntcodeVM

advent.setup(2019, 9, dry_run=True)
fin = advent.get_input()

program = list(map(int, fin.read().split(',')))
vm = IntcodeVM(program)

out = vm.run([1])[-1]

assert out == 4234906522
advent.submit_answer(1, out)

out = vm.run([2])[-1]

assert out == 60962
advent.submit_answer(2, out)
