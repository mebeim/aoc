#!/usr/bin/env python3

from utils import advent

advent.setup(2021, 1)
fin = advent.get_input()

nums = tuple(map(int, fin))
tot  = sum(b > a for a, b in zip(nums, nums[1:]))
advent.print_answer(1, tot)


tot = sum(b > a for a, b in zip(nums, nums[3:]))
advent.print_answer(2, tot)
