#!/usr/bin/env python3

import sys
from lib.intcode import IntcodeVM

# Open the first argument as input or use stdin if no arguments were given
fin = open(sys.argv[1]) if len(sys.argv) > 1 else sys.stdin

program = list(map(int, fin.read().split(',')))
vm = IntcodeVM(program)
out = vm.run([1])[-1]
print('Part 1:', out)

out = vm.run([5])[-1]
print('Part 2:', out)
