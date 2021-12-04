#!/usr/bin/env python3

from utils import advent
from functools import partial

def most_common_bit(nums, shift):
	n_ones = sum(((n >> shift) & 1) for n in nums)
	return 1 if n_ones > len(nums) // 2 - 1 else 0

def least_common_bit(nums, shift):
	return 1 - most_common_bit(nums, shift)

def most_common_bits(nums, n_bits):
	res = 0

	for shift in range(n_bits - 1, -1, -1):
		res <<= 1
		res += most_common_bit(nums, shift)

	return res

def filter_numbers(nums, n_bits, predicate):
	for shift in range(n_bits - 1, -1, -1):
		bit  = predicate(nums, shift)
		nums = tuple(filter(lambda n: (n >> shift) & 1 == bit, nums))

		if len(nums) == 1:
			break

	return nums[0]


advent.setup(2021, 3)
fin = advent.get_input()

lines  = fin.readlines()
n_bits = len(lines[0].strip())
nums   = tuple(map(partial(int, base=2), lines))

gamma = most_common_bits(nums, n_bits)
eps   = (1 << n_bits) - gamma - 1
power = gamma * eps

advent.print_answer(1, power)


oxy    = filter_numbers(nums, n_bits, most_common_bit)
co2    = filter_numbers(nums, n_bits, least_common_bit)
rating = oxy * co2

advent.print_answer(2, rating)
