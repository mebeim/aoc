#!/usr/bin/env python3

import re
from math import gcd
from copy import deepcopy
from collections import deque
from operator import add, mul, attrgetter

from utils import advent


class Monkey:
    __slots__ = (
        'items', 'op', 'op_value', 'divisor',
        'pass_if_true', 'pass_if_false', 'inspections'
    )

    def inspect(self):
        item = self.items.popleft()
        if self.op_value is None:
            return self.op(item, item)
        return self.op(item, self.op_value)

# math.lcm() is Python 3.9+


def lcm(*integers):
    it = iter(integers)
    res = next(it)

    for x in it:
        res = res * x // gcd(res, x)
    return res


def simulate(monkeys, n_rounds, part2=False):
    if part2:
        modulus = lcm(*map(attrgetter('divisor'), monkeys))

    for _ in range(n_rounds):
        for m in monkeys:
            m.inspections += len(m.items)

            while m.items:
                item = m.inspect() % modulus if part2 else m.inspect() // 3
                if item % m.divisor == 0:
                    monkeys[m.pass_if_true].items.append(item)
                else:
                    monkeys[m.pass_if_false].items.append(item)

    a, b = sorted(map(attrgetter('inspections'), monkeys), reverse=True)[:2]
    return a * b


advent.setup(2022, 11)

regexp = re.compile(r'\d+')
monkeys = []

with advent.get_input() as fin:
    raw_monkeys = fin.read().split('\n\n')

for raw_monkey in raw_monkeys:
    lines = raw_monkey.splitlines()
    matches = regexp.findall(lines[2])

    m = Monkey()
    m.items = deque(map(int, regexp.findall(lines[1])))
    m.op = add if '+' in lines[2] else mul
    m.op_value = int(matches[0]) if matches else None
    m.divisor = int(regexp.findall(lines[3])[0])
    m.pass_if_true = int(regexp.findall(lines[4])[0])
    m.pass_if_false = int(regexp.findall(lines[5])[0])
    m.inspections = 0
    monkeys.append(m)

original = deepcopy(monkeys)

answer1 = simulate(monkeys, 20)
advent.print_answer(1, answer1)

answer2 = simulate(original, 10000, True)
advent.print_answer(2, answer2)
