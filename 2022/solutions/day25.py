#!/usr/bin/env python3

from utils import advent

VALUES = {'=': -2, '-': -1, '0': 0, '1': 1, '2': 2}


def base10(n):
    power = 5 ** (len(n) - 1)
    res = 0

    for digit in n:
        res += VALUES[digit] * power
        power //= 5

    return res


def snafu(n):
    res = ''

    while n:
        n, digit = divmod(n, 5)
        res += '012=-'[digit]
        n += digit > 2

    return res[::-1]


advent.setup(2022, 25)
fin = advent.get_input()

answer = snafu(sum(map(base10, fin.read().split())))
advent.print_answer(1, answer)
